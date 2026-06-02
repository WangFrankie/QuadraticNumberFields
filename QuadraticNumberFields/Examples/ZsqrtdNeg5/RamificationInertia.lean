/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang

Computing ramification index and inertia degree for primes 2 and 3 in ℤ[√-5].
Ported from the ANT project.
-/
import QuadraticNumberFields.Examples.ZsqrtdNeg5.Ideals
import Mathlib.NumberTheory.RamificationInertia.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank

/-!
# Ramification and Inertia in ℤ[√-5]

This file computes the ramification indices and inertia degrees for
the primes 2 and 3 in `ℤ[√-5]`, demonstrating the fundamental identity
`∑ eᵢfᵢ = [K:ℚ]` on a concrete example.

## Main Results

### Ramification Index
* `ramificationIdx_P2`: `e(P2|2) = 2` (ramified)
* `ramificationIdx_P3₁`: `e(P3₁|3) = 1` (unramified)
* `ramificationIdx_P3₂`: `e(P3₂|3) = 1` (unramified)

### Inertia Degree
* `inertiaDeg_P2`: `f(P2|2) = 1`
* `inertiaDeg_P3₁`: `f(P3₁|3) = 1`
* `inertiaDeg_P3₂`: `f(P3₂|3) = 1`

### Summary Table

| Prime | Factorization    | e | f | g |
|-------|-----------------|---|---|---|
| 2     | (2) = P2²       | 2 | 1 | 1 |
| 3     | (3) = P3₁ · P3₂ | 1 | 1 | 2 |

Verification: e × f × g = 2 = [ℚ(√-5) : ℚ] ✓
-/

open Ideal

namespace QuadraticNumberFields.Examples.ZsqrtdNeg5

local notation "sqrtd" => _root_.Zsqrtd.sqrtd

/-! ## Prime ideal definitions -/

/-- The prime ideal (2, 1+√-5) in ℤ[√-5] -/
def P2 : Ideal R := span {2, 1 + sqrtd}

/-- The prime ideal (3, 1+√-5) in ℤ[√-5] -/
def P3₁ : Ideal R := span {3, 1 + sqrtd}

/-- The prime ideal (3, 1-√-5) in ℤ[√-5] -/
def P3₂ : Ideal R := span {3, 1 - sqrtd}

/-! ## Helper lemmas (specific to d = -5) -/

/-- Ring hom sending `√-5` to `2` in `ZMod 9`. -/
noncomputable def phiPlus9 : R →+* ZMod 9 :=
  _root_.Zsqrtd.lift ⟨(2 : ZMod 9), by decide⟩

/-- Ring hom sending `√-5` to `-2` in `ZMod 9`. -/
noncomputable def phiMinus9 : R →+* ZMod 9 :=
  _root_.Zsqrtd.lift ⟨((-2 : ℤ) : ZMod 9), by decide⟩

private lemma map_span_pair_le_span3_mod9
    (φ : R →+* ZMod 9) {x y : R}
    (hx : φ x ∈ span ({(3 : ZMod 9)} : Set (ZMod 9)))
    (hy : φ y ∈ span ({(3 : ZMod 9)} : Set (ZMod 9))) :
    map φ (span ({x, y} : Set R)) ≤ span ({(3 : ZMod 9)} : Set (ZMod 9)) := by
  rw [Ideal.map_span, Ideal.span_le]
  intro z hz
  rw [Set.image_pair] at hz
  rcases hz with rfl | rfl <;> assumption

lemma map_P3₁_le_span3_mod9 :
    map phiPlus9 P3₁ ≤ span ({(3 : ZMod 9)} : Set (ZMod 9)) := by
  unfold P3₁
  refine map_span_pair_le_span3_mod9 phiPlus9 ?_ ?_
  · exact Ideal.mem_span_singleton.mpr ⟨1, by decide⟩
  · exact Ideal.mem_span_singleton.mpr ⟨1, by decide⟩

lemma map_P3₂_le_span3_mod9 :
    map phiMinus9 P3₂ ≤ span ({(3 : ZMod 9)} : Set (ZMod 9)) := by
  unfold P3₂
  refine map_span_pair_le_span3_mod9 phiMinus9 ?_ ?_
  · exact Ideal.mem_span_singleton.mpr ⟨1, by decide⟩
  · exact Ideal.mem_span_singleton.mpr ⟨1, by decide⟩

private lemma not_span3_le_sq_of_map_le_span3_mod9
    (φ : R →+* ZMod 9) (P : Ideal R)
    (hP : map φ P ≤ span ({(3 : ZMod 9)} : Set (ZMod 9)))
    (hφ3 : (φ (3 : R) : ZMod 9) = 3) :
    ¬ (span ({(3 : R)} : Set R) : Ideal R) ≤ P ^ (1 + 1) := by
  intro h
  have hmap : map φ (span ({(3 : R)} : Set R)) ≤ map φ (P ^ (1 + 1)) :=
    Ideal.map_mono h
  have hsq : map φ (P ^ (1 + 1)) ≤ ⊥ := by
    calc
      map φ (P ^ (1 + 1)) = (map φ P) ^ (1 + 1) := by
        simpa using (Ideal.map_pow φ P (1 + 1))
      _ = map φ P * map φ P := by simp [pow_two]
      _ ≤ span ({(3 : ZMod 9)} : Set (ZMod 9)) * span ({(3 : ZMod 9)} : Set (ZMod 9)) :=
        Ideal.mul_mono hP hP
      _ = (span ({(3 : ZMod 9)} : Set (ZMod 9)) : Ideal (ZMod 9)) ^ (1 + 1) := by
        simp [pow_two]
      _ = ⊥ := by
        have h9 : ((3 : ZMod 9) ^ 2) = 0 := by decide
        rw [Ideal.span_singleton_pow, h9, Ideal.span_singleton_eq_bot]
  have hbot : map φ (span ({(3 : R)} : Set R)) = ⊥ :=
    le_bot_iff.mp (hmap.trans hsq)
  have hzero : ((3 : ZMod 9)) = 0 := by
    have hzero' : (φ (3 : R) : ZMod 9) = 0 := by
      apply (Ideal.span_singleton_eq_bot.mp _)
      simpa [Ideal.map_span] using hbot
    simpa [hφ3] using hzero'
  exact (by decide : (3 : ZMod 9) ≠ 0) hzero

private theorem ramificationIdx_eq_one_of_le_and_not_sq
    (P : Ideal R)
    (hP : (span ({(3 : R)} : Set R) : Ideal R) ≤ P)
    (hnot : ¬ (span ({(3 : R)} : Set R) : Ideal R) ≤ P ^ (1 + 1)) :
    ramificationIdx (span {(3 : ℤ)}) P = 1 := by
  rw [ramificationIdx_spec]
  · rw [_root_.Zsqrtd.Ideal.map_span_int_singleton, pow_one]
    simpa using hP
  · intro h
    rw [_root_.Zsqrtd.Ideal.map_span_int_singleton] at h
    exact hnot h

lemma not_span3_le_P3₁_sq : ¬(span ({(3 : R)} : Set R) : Ideal R) ≤ P3₁ ^ (1 + 1) := by
  refine not_span3_le_sq_of_map_le_span3_mod9 phiPlus9 P3₁ map_P3₁_le_span3_mod9 ?_
  simp [phiPlus9]

lemma not_span3_le_P3₂_sq : ¬(span ({(3 : R)} : Set R) : Ideal R) ≤ P3₂ ^ (1 + 1) := by
  refine not_span3_le_sq_of_map_le_span3_mod9 phiMinus9 P3₂ map_P3₂_le_span3_mod9 ?_
  simp [phiMinus9]

/-! ## Comap and quotient lemmas (instantiated from general theory) -/

instance : Fact (Nat.Prime 2) := ⟨by decide⟩
instance : Fact (Nat.Prime 3) := ⟨by decide⟩

lemma comap_P2 : Ideal.comap (algebraMap ℤ R) P2 = (span ({(2 : ℤ)} : Set ℤ) : Ideal ℤ) :=
  _root_.Zsqrtd.Ideal.comap_span_p_one_plus_sqrtd 2 neg5_dvd_two

lemma comap_P3₁ : Ideal.comap (algebraMap ℤ R) P3₁ = (span ({(3 : ℤ)} : Set ℤ) : Ideal ℤ) :=
  _root_.Zsqrtd.Ideal.comap_span_p_one_plus_sqrtd 3 neg5_dvd_three

lemma comap_P3₂ : Ideal.comap (algebraMap ℤ R) P3₂ = (span ({(3 : ℤ)} : Set ℤ) : Ideal ℤ) :=
  _root_.Zsqrtd.Ideal.comap_span_p_one_minus_sqrtd 3 neg5_dvd_three

/-- The quotient by `P2` is canonically isomorphic to `ZMod 2`. -/
noncomputable def quotEquivP2 : (R ⧸ P2) ≃+* ZMod 2 :=
  _root_.Zsqrtd.Ideal.quotEquivZModPNeg 2 neg5_dvd_two

/-- The quotient by `P3₁` is canonically isomorphic to `ZMod 3`. -/
noncomputable def quotEquivP3₁ : (R ⧸ P3₁) ≃+* ZMod 3 :=
  _root_.Zsqrtd.Ideal.quotEquivZModPNeg 3 neg5_dvd_three

/-- The quotient by `P3₂` is canonically isomorphic to `ZMod 3`. -/
noncomputable def quotEquivP3₂ : (R ⧸ P3₂) ≃+* ZMod 3 :=
  _root_.Zsqrtd.Ideal.quotEquivZModP 3 neg5_dvd_three

/-! ## Main Results: Ramification Index -/

/-- The ramification index of P2 over (2) is 2.

Mathematical reason: (2) = P2² in ℤ[√-5], so 2 = e(P2|2) × f(P2|2) = 2 × 1.
This means P2 appears with exponent 2 in the factorization of (2). -/
theorem ramificationIdx_P2 :
    ramificationIdx (span {(2 : ℤ)}) P2 = 2 := by
  rw [ramificationIdx_spec]
  · rw [_root_.Zsqrtd.Ideal.map_span_int_singleton]
    convert le_refl _ using 1
    exact factorization_of_two.symm
  · intro h
    have hprime : (P2 : Ideal R).IsPrime := by
      simpa [P2] using isPrime_span_two_one_plus_sqrtd
    have hne_top : (P2 : Ideal R) ≠ ⊤ := hprime.ne_top
    have h2ne : (2 : R) ≠ 0 := by norm_num
    have h' : (span ({(2 : R)} : Set R) : Ideal R) * ⊤ ≤
        (span ({(2 : R)} : Set R) : Ideal R) * P2 := by
      rw [_root_.Zsqrtd.Ideal.map_span_int_singleton] at h
      simpa [pow_succ, factorization_of_two, Ideal.mul_assoc] using h
    have htop_le : (⊤ : Ideal R) ≤ P2 :=
      (Ideal.span_singleton_mul_right_mono (I := (⊤ : Ideal R)) (J := P2) h2ne).1 h'
    exact hne_top (top_le_iff.mp htop_le)

/-- The ramification index of P3₁ over (3) is 1.

Mathematical reason: (3) = P3₁ · P3₂, so P3₁ appears with exponent 1. -/
theorem ramificationIdx_P3₁ :
    ramificationIdx (span {(3 : ℤ)}) P3₁ = 1 :=
  ramificationIdx_eq_one_of_le_and_not_sq P3₁
    (by
      rw [factorization_of_three]
      exact Ideal.mul_le_right)
    not_span3_le_P3₁_sq

/-- The ramification index of P3₂ over (3) is 1. -/
theorem ramificationIdx_P3₂ :
    ramificationIdx (span {(3 : ℤ)}) P3₂ = 1 :=
  ramificationIdx_eq_one_of_le_and_not_sq P3₂
    (by
      rw [factorization_of_three]
      exact Ideal.mul_le_left)
    not_span3_le_P3₂_sq

/-! ## Main Results: Inertia Degree -/

/-- The inertia degree of P2 over (2) is 1.

Mathematical reason: ℤ[√-5]/(2, 1+√-5) ≅ ℤ/2ℤ, so the residue field has size 2,
which as a vector space over ℤ/2ℤ has dimension 1. -/
theorem inertiaDeg_P2 :
    inertiaDeg (span {(2 : ℤ)}) P2 = 1 := by
  letI : Algebra (ℤ ⧸ (span ({(2 : ℤ)} : Set ℤ) : Ideal ℤ)) (R ⧸ P2) :=
    Ideal.Quotient.algebraQuotientOfLEComap (le_of_eq comap_P2.symm)
  rw [Ideal.inertiaDeg, dif_pos comap_P2]
  have hfin := Algebra.finrank_eq_of_equiv_equiv (Int.quotientSpanNatEquivZMod 2) quotEquivP2 (by
    ext n
    simp [quotEquivP2, _root_.Zsqrtd.Ideal.quotEquivZModPNeg, _root_.Zsqrtd.Ideal.liftModPNeg, P2]
  )
  exact_mod_cast hfin.trans (by simp [Module.finrank_self])

/-- The inertia degree of P3₁ over (3) is 1. -/
theorem inertiaDeg_P3₁ :
    inertiaDeg (span {(3 : ℤ)}) P3₁ = 1 := by
  letI : Algebra (ℤ ⧸ (span ({(3 : ℤ)} : Set ℤ) : Ideal ℤ)) (R ⧸ P3₁) :=
    Ideal.Quotient.algebraQuotientOfLEComap (le_of_eq comap_P3₁.symm)
  rw [Ideal.inertiaDeg, dif_pos comap_P3₁]
  have hfin := Algebra.finrank_eq_of_equiv_equiv (Int.quotientSpanNatEquivZMod 3) quotEquivP3₁ (by
    ext n
    simp [quotEquivP3₁, _root_.Zsqrtd.Ideal.quotEquivZModPNeg, _root_.Zsqrtd.Ideal.liftModPNeg, P3₁]
  )
  exact_mod_cast hfin.trans (by simp [Module.finrank_self])

/-- The inertia degree of P3₂ over (3) is 1. -/
theorem inertiaDeg_P3₂ :
    inertiaDeg (span {(3 : ℤ)}) P3₂ = 1 := by
  letI : Algebra (ℤ ⧸ (span ({(3 : ℤ)} : Set ℤ) : Ideal ℤ)) (R ⧸ P3₂) :=
    Ideal.Quotient.algebraQuotientOfLEComap (le_of_eq comap_P3₂.symm)
  rw [Ideal.inertiaDeg, dif_pos comap_P3₂]
  have hfin := Algebra.finrank_eq_of_equiv_equiv (Int.quotientSpanNatEquivZMod 3) quotEquivP3₂ (by
    ext n
    simp [quotEquivP3₂, _root_.Zsqrtd.Ideal.quotEquivZModP, _root_.Zsqrtd.Ideal.liftModP, P3₂]
  )
  exact_mod_cast hfin.trans (by simp [Module.finrank_self])

end QuadraticNumberFields.Examples.ZsqrtdNeg5

--TODO : using Discriminant, show that 2 is the only ramified prime in ℤ[√-5],
-- and that all other primes are either inert or split.

-- Discriminant of ℤ[√d] is 4d if d ≡ 2,3 mod 4, and d if d ≡ 1 mod 4. For d = -5,
-- we have 4d = -20, which is divisible by 2 but not by any other prime,
-- so 2 is the only ramified prime.
