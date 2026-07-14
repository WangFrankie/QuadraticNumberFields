/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/

import Mathlib.NumberTheory.Pell
import QNFMathlib.RingTheory.Ideal.Norm.AbsNorm
import QuadraticNumberFields.ClassGroup.Ambiguous.RamifiedParity
import QuadraticNumberFields.ClassGroup.Ambiguous.Relation.SquareNorm
import QuadraticNumberFields.ClassGroup.Narrow.Principal
import QuadraticNumberFields.Qsqrtd.TotallyRealComplex
import QuadraticNumberFields.Splitting.Qsqrtd.SqrtD
import QuadraticNumberFields.Units.Pell

/-!
# Real-Quadratic Pell Layer for the Ramified-Parity Relation

This file transports Pell units from `ℤ[√d]` to `𝓞(ℚ(√d))`, constructs
totally-positive / positive-norm generators, proves the Pell half-argument and
`Nat.factorization` divisibility chain, and builds the real-case ambiguous
narrow-principal ideal.
-/

namespace QuadraticNumberFields
namespace ClassGroup
namespace Ambiguous

open scoped NumberField nonZeroDivisors
open scoped QuadraticNumberFields.Splitting

attribute [-instance] DivisionRing.toRatAlgebra

section Qsqrtd

variable (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)]

local notation "OK" => NumberField.RingOfIntegers (Qsqrtd (d : ℚ))
local notation "conjOK" => conjAutRingOfIntegers (Qsqrtd (d : ℚ))

private theorem exists_tp_generator_of_qsqrt_norm_pos
    (hd : 0 < d)
    {r : RamifiedParityVector d}
    {γ : (FractionRing OK)ˣ}
    (hγ :
      toPrincipalIdeal OK (FractionRing OK) γ =
        FractionalIdeal.mk0 (FractionRing OK) (fullRamifiedParityIdealProduct d r))
    (hNormPos :
      0 <
        (Qsqrtd.norm
          (FractionRing.algEquiv OK (Qsqrtd (d : ℚ)) (γ : FractionRing OK)) : ℝ)) :
    ∃ δ : (FractionRing OK)ˣ,
      NarrowClassGroup.IsTotallyPositive (δ : FractionRing OK) ∧
        toPrincipalIdeal OK (FractionRing OK) δ =
          FractionalIdeal.mk0 (FractionRing OK) (fullRamifiedParityIdealProduct d r) := by
  rcases Qsqrtd.Real.isTotallyPositive_or_neg_isTotallyPositive_of_norm_pos
    d hd hNormPos with hpos | hneg
  · exact ⟨γ, hpos, hγ⟩
  · refine ⟨-γ, hneg, ?_⟩
    rw [NarrowClassGroup.toPrincipalIdeal_neg, hγ]

private theorem exists_positive_norm_generator_of_real_of_negative_norm_unit
    (hprincipal :
      ∃ r : RamifiedParityVector d,
        (∃ p, r p ≠ 0) ∧
          ∃ γ : (FractionRing OK)ˣ,
            toPrincipalIdeal OK (FractionRing OK) γ =
              FractionalIdeal.mk0 (FractionRing OK) (fullRamifiedParityIdealProduct d r))
    (hnegUnit :
      ∃ ε : OKˣ,
        let εK : (FractionRing OK)ˣ :=
          Units.map (algebraMap OK (FractionRing OK)).toMonoidHom ε
        (Qsqrtd.norm
          (FractionRing.algEquiv OK (Qsqrtd (d : ℚ)) (εK : FractionRing OK)) : ℝ) < 0) :
    ∃ r : RamifiedParityVector d,
      (∃ p, r p ≠ 0) ∧
        ∃ γ : (FractionRing OK)ˣ,
          toPrincipalIdeal OK (FractionRing OK) γ =
              FractionalIdeal.mk0 (FractionRing OK) (fullRamifiedParityIdealProduct d r) ∧
            0 <
              (Qsqrtd.norm
                (FractionRing.algEquiv OK (Qsqrtd (d : ℚ)) (γ : FractionRing OK)) : ℝ) := by
  classical
  obtain ⟨ε, hεNormNeg⟩ := hnegUnit
  obtain ⟨r, hrnonzero, γ, hγ⟩ := hprincipal
  let z : Qsqrtd (d : ℚ) :=
    FractionRing.algEquiv OK (Qsqrtd (d : ℚ)) (γ : FractionRing OK)
  let n : ℝ := (Qsqrtd.norm z : ℝ)
  have hz_ne : z ≠ 0 :=
    (map_ne_zero (FractionRing.algEquiv OK (Qsqrtd (d : ℚ))).toRingHom).mpr
      (Units.ne_zero γ)
  have hn_ne : n ≠ 0 := by
    have hnorm_ne : Qsqrtd.norm z ≠ 0 :=
      fun hnorm => hz_ne (QuadraticAlgebra.norm_eq_zero_iff_eq_zero.mp hnorm)
    have hnorm_ne_real : ((Qsqrtd.norm z : ℚ) : ℝ) ≠ 0 := by
      exact_mod_cast hnorm_ne
    simpa [n] using hnorm_ne_real
  rcases lt_trichotomy n 0 with hn_neg | hn_zero | hn_pos
  · let εK : (FractionRing OK)ˣ :=
      Units.map (algebraMap OK (FractionRing OK)).toMonoidHom ε
    have hγε :
        toPrincipalIdeal OK (FractionRing OK) (γ * εK) =
          FractionalIdeal.mk0 (FractionRing OK) (fullRamifiedParityIdealProduct d r) := by
      rw [NarrowClassGroup.toPrincipalIdeal_mul_algebraMap_unit, hγ]
    have hγNormNeg :
        (Qsqrtd.norm
          (FractionRing.algEquiv OK (Qsqrtd (d : ℚ)) (γ : FractionRing OK)) : ℝ) < 0 := by
      simpa [n, z] using hn_neg
    have hNormPos :
        0 <
          (Qsqrtd.norm
            (FractionRing.algEquiv OK (Qsqrtd (d : ℚ))
              ((γ * εK : (FractionRing OK)ˣ) : FractionRing OK)) : ℝ) :=
      by
        simpa [map_mul, εK] using
          mul_pos_of_neg_of_neg hγNormNeg hεNormNeg
    exact ⟨r, hrnonzero, γ * εK, hγε, hNormPos⟩
  · exact False.elim (hn_ne hn_zero)
  · exact ⟨r, hrnonzero, γ, hγ, by simpa [n, z] using hn_pos⟩

private theorem exists_nonzero_ramifiedParity_tp_generator_of_real_of_negative_norm_unit
    (hd : 0 < d)
    (hprincipal :
      ∃ r : RamifiedParityVector d,
        (∃ p, r p ≠ 0) ∧
          ∃ γ : (FractionRing OK)ˣ,
            toPrincipalIdeal OK (FractionRing OK) γ =
              FractionalIdeal.mk0 (FractionRing OK) (fullRamifiedParityIdealProduct d r))
    (hnegUnit :
      ∃ ε : OKˣ,
        let εK : (FractionRing OK)ˣ :=
          Units.map (algebraMap OK (FractionRing OK)).toMonoidHom ε
        (Qsqrtd.norm
          (FractionRing.algEquiv OK (Qsqrtd (d : ℚ)) (εK : FractionRing OK)) : ℝ) < 0) :
    ∃ r : RamifiedParityVector d,
      (∃ p, r p ≠ 0) ∧
        ∃ γ : (FractionRing OK)ˣ,
          NarrowClassGroup.IsTotallyPositive (γ : FractionRing OK) ∧
            toPrincipalIdeal OK (FractionRing OK) γ =
              FractionalIdeal.mk0 (FractionRing OK) (fullRamifiedParityIdealProduct d r) := by
  obtain ⟨r, hrnonzero, γ, hγ, hγNormPos⟩ :=
    exists_positive_norm_generator_of_real_of_negative_norm_unit
      d hprincipal hnegUnit
  obtain ⟨δ, hδpos, hδ⟩ := exists_tp_generator_of_qsqrt_norm_pos d hd hγ hγNormPos
  exact ⟨r, hrnonzero, δ, hδpos, hδ⟩

private theorem one_add_unit_ne_zero_of_ne_neg_one
    (u : OKˣ) (hu_ne_neg_one : u ≠ -1) :
    (1 + (u : OK)) ≠ 0 := by
  intro hα
  exact hu_ne_neg_one (Units.ext (eq_neg_of_add_eq_zero_left (by simpa [add_comm] using hα)))

private noncomputable def unitOfPellSolution (a : Pell.Solution₁ d) : OKˣ :=
  let h : QuadraticNumberFields.Units.IsPellUnitSolution d a.x a.y := a.prop
  Units.map (Splitting.zsqrtdEmbedding d).toMonoidHom h.unit

private theorem unitOfPellSolution_val (a : Pell.Solution₁ d) :
    (unitOfPellSolution d a : OK) =
      algebraMap ℤ OK a.x + algebraMap ℤ OK a.y * Splitting.sqrtdInt d := by
  simp [unitOfPellSolution, Splitting.zsqrtdEmbedding_apply]

private theorem unitOfPellSolution_conjAut_mul_self_eq_one (a : Pell.Solution₁ d) :
    Units.mapEquiv (conjOK).toMulEquiv
        (unitOfPellSolution d a) *
      unitOfPellSolution d a = 1 := by
  let K := Qsqrtd (d : ℚ)
  let α : OK := algebraMap ℤ OK a.x + algebraMap ℤ OK a.y * Splitting.sqrtdInt d
  let β : OK := algebraMap ℤ OK a.x - algebraMap ℤ OK a.y * Splitting.sqrtdInt d
  have hval : (unitOfPellSolution d a : OK) = α := by
    simpa [α] using unitOfPellSolution_val d a
  have hconj : conjAutRingOfIntegers K (unitOfPellSolution d a : OK) = β := by
    rw [hval]
    simpa [α, β, K] using
      Splitting.conjAutRingOfIntegers_intCast_add_intCast_mul_sqrtdInt d a.x a.y
  have hinv : (↑((unitOfPellSolution d a)⁻¹) : OK) = β := by
    simp [unitOfPellSolution, QuadraticNumberFields.Units.IsPellUnitSolution.unit,
      QuadraticAlgebra.unitOfNormOne, Splitting.zsqrtdEmbedding_apply, β,
      sub_eq_add_neg]
  exact Units.ext (by
    change conjAutRingOfIntegers K (unitOfPellSolution d a : OK) *
        (unitOfPellSolution d a : OK) = (1 : OK)
    rw [hconj, ← hinv]
    exact Units.inv_mul (unitOfPellSolution d a))

private theorem unitOfPellSolution_ne_one_of_y_ne_zero
    {a : Pell.Solution₁ d} (ha_y : a.y ≠ 0) :
    unitOfPellSolution d a ≠ 1 := by
  let h : QuadraticNumberFields.Units.IsPellUnitSolution d a.x a.y := a.prop
  simpa [unitOfPellSolution] using
    (Units.map_injective (Splitting.zsqrtdEmbedding_injective d)).ne
      (h.unit_ne_one ha_y)

private theorem unitOfPellSolution_ne_neg_one_of_y_ne_zero
    {a : Pell.Solution₁ d} (ha_y : a.y ≠ 0) :
    unitOfPellSolution d a ≠ -1 := by
  let h : QuadraticNumberFields.Units.IsPellUnitSolution d a.x a.y := a.prop
  simpa [unitOfPellSolution] using
    (Units.map_injective (Splitting.zsqrtdEmbedding_injective d)).ne
      (h.unit_ne_neg_one ha_y)

private theorem exists_fundamental_pell_unit_of_real (hd : 0 < d) :
    ∃ a : Pell.Solution₁ d,
      Pell.IsFundamental a ∧
        let u := unitOfPellSolution d a
        u ≠ 1 ∧
          u ≠ -1 ∧
            Units.mapEquiv (conjOK).toMulEquiv u * u = 1 := by
  have hsq : ¬ IsSquare d :=
    not_isSquare_int_of_squarefree_ne_one (Fact.out : Squarefree d) (Fact.out : d ≠ 1)
  obtain ⟨a, ha⟩ := Pell.IsFundamental.exists_of_not_isSquare hd hsq
  refine ⟨a, ha, ?_, ?_, ?_⟩
  · exact unitOfPellSolution_ne_one_of_y_ne_zero d (ne_of_gt ha.2.1)
  · exact unitOfPellSolution_ne_neg_one_of_y_ne_zero d (ne_of_gt ha.2.1)
  · exact unitOfPellSolution_conjAut_mul_self_eq_one d a

private theorem unitOfPellSolution_isTotallyPositive_of_pos
    (hd : 0 < d) {a : Pell.Solution₁ d} (hax : 0 < a.x) (hay : 0 < a.y) :
    let uK : (FractionRing OK)ˣ :=
      Units.map (algebraMap OK (FractionRing OK)).toMonoidHom (unitOfPellSolution d a)
    NarrowClassGroup.IsTotallyPositive (uK : FractionRing OK) := by
  intro uK σ
  let K := Qsqrtd (d : ℚ)
  let e : FractionRing OK ≃ₐ[OK] K := FractionRing.algEquiv OK K
  let z : K := e (uK : FractionRing OK)
  have hz : z = (⟨(a.x : ℚ), (a.y : ℚ)⟩ : K) := by
    have hmap : e (uK : FractionRing OK) = ((unitOfPellSolution d a : OK) : K) := by
      simp [e, uK, K]
    have hval :
        (unitOfPellSolution d a : OK) =
          algebraMap ℤ OK a.x + algebraMap ℤ OK a.y * Splitting.sqrtdInt d := by
      simpa using unitOfPellSolution_val d a
    change e (uK : FractionRing OK) = (⟨(a.x : ℚ), (a.y : ℚ)⟩ : K)
    rw [hmap, hval]
    exact Splitting.coe_intCast_add_intCast_mul_sqrtdInt d a.x a.y
  have hd_nonneg_real : 0 ≤ (d : ℝ) := by exact_mod_cast le_of_lt hd
  have hpos :
      0 < Qsqrtd.realEmbeddingPos d hd_nonneg_real z := by
    rw [hz, Qsqrtd.realEmbeddingPos_apply]
    have hxR : 0 < (a.x : ℝ) := by exact_mod_cast hax
    have hyR : 0 ≤ (a.y : ℝ) := by exact_mod_cast le_of_lt hay
    exact add_pos_of_pos_of_nonneg hxR (mul_nonneg hyR (Real.sqrt_nonneg _))
  have hnorm : (Qsqrtd.norm z : ℝ) = 1 := by
    rw [hz]
    simp only [Qsqrtd.norm, QuadraticAlgebra.norm_def]
    norm_num
    have hprop : a.x * a.x - d * a.y * a.y = 1 := by
      nlinarith [a.prop]
    exact_mod_cast hprop
  have hneg :
      0 < Qsqrtd.realEmbeddingNeg d hd_nonneg_real z := by
    have hmul :
        Qsqrtd.realEmbeddingPos d hd_nonneg_real z *
            Qsqrtd.realEmbeddingNeg d hd_nonneg_real z = 1 := by
      rw [← Qsqrtd.norm_eq_realEmbeddingPos_mul_realEmbeddingNeg d hd_nonneg_real z,
        hnorm]
    exact pos_of_mul_pos_right (by rw [hmul]; exact zero_lt_one) hpos.le
  rcases Qsqrtd.fractionRing_ringHom_eq_realEmbeddingPos_or_neg
    d hd_nonneg_real σ with hσ | hσ
  · rw [hσ]
    simpa [z, e, K, RingHom.comp_apply] using hpos
  · rw [hσ]
    simpa [z, e, K, RingHom.comp_apply] using hneg

private theorem algebraNorm_one_add_unitOfPellSolution (a : Pell.Solution₁ d) :
    Algebra.norm ℤ (1 + (unitOfPellSolution d a : OK)) = 2 * (a.x + 1) := by
  let K := Qsqrtd (d : ℚ)
  apply Int.cast_injective (α := ℚ)
  rw [Algebra.coe_norm_int (K := K), Qsqrtd.algebraNorm_ratAlgebra_eq_qsqrtdNorm]
  have hval :
      (unitOfPellSolution d a : OK) =
        algebraMap ℤ OK a.x + algebraMap ℤ OK a.y * Splitting.sqrtdInt d := by
    simpa using unitOfPellSolution_val d a
  have hcoord :
      ((1 + (unitOfPellSolution d a : OK) : OK) : K) =
        (⟨((a.x + 1 : ℤ) : ℚ), (a.y : ℚ)⟩ : K) := by
    rw [hval]
    convert Splitting.coe_intCast_add_intCast_mul_sqrtdInt d (a.x + 1) a.y using 1
    simp [map_add, add_assoc, add_comm]
  rw [hcoord]
  simp only [Qsqrtd.norm, QuadraticAlgebra.norm_def, Int.cast_add, Int.cast_one,
    Int.cast_mul, Int.cast_ofNat]
  have hprop : ((a.x : ℚ) ^ 2 - (d : ℚ) * (a.y : ℚ) ^ 2 : ℚ) = 1 := by
    exact_mod_cast a.prop
  ring_nf at hprop ⊢
  nlinarith

private theorem absNorm_span_one_add_unitOfPellSolution (a : Pell.Solution₁ d) :
    Ideal.absNorm (Ideal.span ({1 + (unitOfPellSolution d a : OK)} : Set OK)) =
      (2 * (a.x + 1)).natAbs := by
  rw [Ideal.absNorm_span_singleton, algebraNorm_one_add_unitOfPellSolution]

omit [Fact (Squarefree d)] [Fact (d ≠ 1)] in
private theorem two_mul_x_add_one_pos_of_isFundamental {a : Pell.Solution₁ d}
    (ha : Pell.IsFundamental a) :
    0 < 2 * (a.x + 1) := by
  nlinarith [ha.1]

private theorem natAbs_eq_toNat_of_pos {z : ℤ} (hz : 0 < z) : z.natAbs = z.toNat := by
  apply Nat.cast_injective (R := ℤ)
  rw [Int.natAbs_of_nonneg (le_of_lt hz), Int.toNat_of_nonneg (le_of_lt hz)]

private theorem int_toNat_ne_zero_of_pos {z : ℤ} (hz : 0 < z) : z.toNat ≠ 0 :=
  Nat.ne_of_gt (Int.ofNat_lt.mp (by simpa [Int.toNat_of_nonneg (le_of_lt hz)] using hz))

private theorem absNorm_span_one_add_unitOfPellSolution_of_isFundamental
    {a : Pell.Solution₁ d} (ha : Pell.IsFundamental a) :
    Ideal.absNorm (Ideal.span ({1 + (unitOfPellSolution d a : OK)} : Set OK)) =
      Int.toNat (2 * (a.x + 1)) := by
  rw [absNorm_span_one_add_unitOfPellSolution]
  exact natAbs_eq_toNat_of_pos (two_mul_x_add_one_pos_of_isFundamental d ha)

omit [Fact (Squarefree d)] [Fact (d ≠ 1)] in
private theorem pell_isFundamental_not_sq {a : Pell.Solution₁ d}
    (ha : Pell.IsFundamental a) :
    ¬ ∃ b : Pell.Solution₁ d, b ^ 2 = a := by
  rintro ⟨b, hb⟩
  rcases ha.eq_zpow_or_neg_zpow b with ⟨n, hbna | hbna⟩
  all_goals
    have hpow : a ^ (2 * n : ℤ) = a := by
      calc
        a ^ (2 * n : ℤ) = (a ^ n) ^ (2 : ℤ) := by
          rw [zpow_mul']
        _ = b ^ 2 := by
          rw [hbna]
          try simp
          rfl
        _ = a := hb
    have hone : a ^ (2 * n - 1 : ℤ) = 1 := by
      calc
        a ^ (2 * n - 1 : ℤ) = a ^ (2 * n : ℤ) * a ^ (-1 : ℤ) := by
          rw [sub_eq_add_neg, zpow_add]
        _ = a * a ^ (-1 : ℤ) := by rw [hpow]
        _ = 1 := by simp
    have hzero := (ha.zpow_eq_one_iff (2 * n - 1)).mp hone
    omega

private theorem exists_int_sq_eq_of_isSquare_toNat_of_pos {n : ℤ} (hn : 0 < n)
    (hsq : IsSquare n.toNat) :
    ∃ m : ℤ, 0 ≤ m ∧ m ^ 2 = n := by
  rcases hsq with ⟨m, hm⟩
  refine ⟨m, by positivity, ?_⟩
  rw [← Int.toNat_of_nonneg (le_of_lt hn), hm]
  norm_num [pow_two]

private theorem exists_half_of_nonneg_sq_eq_two_mul {x m : ℤ} (hm0 : 0 ≤ m)
    (hm : m ^ 2 = 2 * (x + 1)) :
    ∃ r : ℤ, 0 ≤ r ∧ m = 2 * r ∧ x + 1 = 2 * r ^ 2 := by
  have h2dvd_m_sq : (2 : ℤ) ∣ m ^ 2 := by
    simp [hm]
  obtain ⟨r, hr⟩ := (show Prime (2 : ℤ) by norm_num).dvd_of_dvd_pow h2dvd_m_sq
  refine ⟨r, by nlinarith, hr, ?_⟩
  nlinarith [hm, hr]

private theorem nat_factorization_four (p : ℕ) :
    (4 : ℕ).factorization p = if p = 2 then 2 else 0 := by
  rw [show (4 : ℕ) = 2 ^ 2 by norm_num]
  rw [Nat.Prime.factorization_pow Nat.prime_two]
  by_cases hp2 : p = 2 <;> simp [hp2]

private theorem nat_factorization_two_of_prime {p : ℕ} (hp : p.Prime) :
    (2 : ℕ).factorization p = if p = 2 then 1 else 0 := by
  by_cases hp2 : p = 2
  · subst hp2
    simp [Nat.Prime.factorization_self Nat.prime_two]
  · simp [hp2, Nat.factorization_eq_zero_of_not_dvd
      (fun hpdiv => hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp hpdiv))]

private theorem nat_factorization_two_mul_of_prime
    {R p : ℕ} (hR0 : R ≠ 0) (hp : p.Prime) :
    (2 * R).factorization p = (if p = 2 then 1 else 0) + R.factorization p := by
  have h2 : (2 : ℕ) ≠ 0 := by norm_num
  rw [Nat.factorization_mul h2 hR0]
  simp [nat_factorization_two_of_prime hp]

private theorem nat_factorization_eq_of_pell_half
    {D R Y : ℕ} (hD0 : D ≠ 0) (hY0 : Y ≠ 0) (hR0 : R ≠ 0)
    (hRm1 : R ^ 2 - 1 ≠ 0)
    (hEq : D * Y ^ 2 = 4 * R ^ 2 * (R ^ 2 - 1)) (p : ℕ) :
    D.factorization p + 2 * Y.factorization p =
      (if p = 2 then 2 else 0) + 2 * R.factorization p +
        (R ^ 2 - 1).factorization p := by
  have h4 : (4 : ℕ) ≠ 0 := by norm_num
  have hR2 : R ^ 2 ≠ 0 := pow_ne_zero 2 hR0
  have hfac := congrArg (fun n : ℕ => n.factorization p) hEq
  change (D * Y ^ 2).factorization p =
    (4 * R ^ 2 * (R ^ 2 - 1)).factorization p at hfac
  rw [Nat.factorization_mul hD0 (pow_ne_zero 2 hY0), Nat.factorization_pow,
    Nat.factorization_mul (mul_ne_zero h4 hR2) hRm1,
    Nat.factorization_mul h4 hR2, Nat.factorization_pow] at hfac
  simpa [nat_factorization_four p, two_nsmul, two_mul, add_assoc] using hfac

private theorem factorization_sq_sub_one_eq_zero_of_prime_dvd
    {p R : ℕ} (hR0 : R ≠ 0) (hp : p.Prime) (hpR : p ∣ R) :
    (R ^ 2 - 1).factorization p = 0 := by
  apply Nat.factorization_eq_zero_of_not_dvd
  intro hpRm1
  have hpR2 : p ∣ R ^ 2 := dvd_pow hpR (by norm_num : 2 ≠ 0)
  have hle : 1 ≤ R ^ 2 := by
    nlinarith [Nat.pos_of_ne_zero hR0]
  have hcop : Nat.Coprime (R ^ 2) (R ^ 2 - 1) :=
    (Nat.coprime_self_sub_right hle).mpr (Nat.coprime_one_right _)
  exact hp.ne_one (Nat.eq_one_of_dvd_coprimes hcop hpR2 hpRm1)

private theorem two_dvd_y_of_squarefree_mul_square
    {D Y : ℕ} (hDsq : Squarefree D) (h4 : (4 : ℕ) ∣ D * Y ^ 2) :
    2 ∣ Y := by
  have h2sq : (2 : ℕ) * 2 ∣ D * Y ^ 2 := by simpa using h4
  have h2Ysq : (2 : ℕ) ∣ Y ^ 2 :=
    Squarefree.dvd_of_squarefree_of_mul_dvd_mul_right hDsq h2sq
  exact Nat.prime_two.dvd_of_dvd_pow h2Ysq

private theorem nat_two_mul_dvd_y_of_squarefree_pell_half
    {D R Y : ℕ} (hDsq : Squarefree D) (hD0 : D ≠ 0) (hY0 : Y ≠ 0)
    (hR0 : R ≠ 0) (hRm1 : R ^ 2 - 1 ≠ 0)
    (hEq : D * Y ^ 2 = 4 * R ^ 2 * (R ^ 2 - 1)) :
    2 * R ∣ Y := by
  have htwoY : 2 ∣ Y := by
    apply two_dvd_y_of_squarefree_mul_square hDsq
    rw [hEq]
    simp [mul_assoc, dvd_mul_right]
  rw [← (Nat.factorization_le_iff_dvd (mul_ne_zero (by norm_num) hR0) hY0)]
  intro p
  by_cases hp : p.Prime
  · rw [nat_factorization_two_mul_of_prime hR0 hp]
    by_cases hpR : p ∣ R
    · have hRm1fac := factorization_sq_sub_one_eq_zero_of_prime_dvd hR0 hp hpR
      have hfac := nat_factorization_eq_of_pell_half hD0 hY0 hR0 hRm1 hEq p
      rw [hRm1fac] at hfac
      have hDle : D.factorization p ≤ 1 :=
        (Nat.squarefree_iff_factorization_le_one hD0).mp hDsq p
      by_cases hp2 : p = 2
      · subst p
        simp at hfac ⊢
        omega
      · simp [hp2] at hfac ⊢
        omega
    · by_cases hp2 : p = 2
      · subst p
        simp [Nat.factorization_eq_zero_of_not_dvd hpR]
        have hle :=
          (Nat.factorization_le_iff_dvd (by norm_num : (2 : ℕ) ≠ 0) hY0).mpr htwoY
        simpa [Nat.Prime.factorization_self Nat.prime_two] using hle 2
      · simp [hp2, Nat.factorization_eq_zero_of_not_dvd hpR]
  · simp [Nat.factorization_eq_zero_of_not_prime _ hp]

omit [Fact (d ≠ 1)] in
private theorem two_mul_dvd_y_of_pell_half
    {a : Pell.Solution₁ d} {r : ℤ}
    (ha : Pell.IsFundamental a) (hr0 : 0 ≤ r) (hx : a.x + 1 = 2 * r ^ 2) :
    2 * r ∣ a.y := by
  let D : ℕ := d.toNat
  let R : ℕ := r.toNat
  let Y : ℕ := a.y.toNat
  have hdpos : 0 < d := ha.d_pos
  have hypos : 0 < a.y := ha.2.1
  have hrpos : 0 < r := lt_of_le_of_ne' hr0 (fun hr => by nlinarith [ha.1, hx])
  have hDcast : (D : ℤ) = d := Int.toNat_of_nonneg (le_of_lt hdpos)
  have hYcast : (Y : ℤ) = a.y := Int.toNat_of_nonneg (le_of_lt hypos)
  have hRcast : (R : ℤ) = r := Int.toNat_of_nonneg hr0
  have hDsq : Squarefree D := by
    simpa [D, natAbs_eq_toNat_of_pos hdpos] using
      Int.squarefree_natAbs.mpr (Fact.out : Squarefree d)
  have hD0 : D ≠ 0 := int_toNat_ne_zero_of_pos hdpos
  have hY0 : Y ≠ 0 := int_toNat_ne_zero_of_pos hypos
  have hR0 : R ≠ 0 := int_toNat_ne_zero_of_pos hrpos
  have hRm1 : R ^ 2 - 1 ≠ 0 := by
    have hRgt1 : 1 < R ^ 2 := by
      apply Int.ofNat_lt.mp
      have hr2gt1 : 1 < r ^ 2 := by nlinarith [ha.1, hx]
      simpa [hRcast] using hr2gt1
    omega
  have hR2cast : ((R ^ 2 : ℕ) : ℤ) = r ^ 2 := by
    norm_num [hRcast]
  have hEqInt : d * a.y ^ 2 = 4 * r ^ 2 * (r ^ 2 - 1) := by
    have hx' : a.x = 2 * r ^ 2 - 1 := by omega
    rw [a.prop_y, hx']
    ring
  have hRm1cast : ((R ^ 2 - 1 : ℕ) : ℤ) = r ^ 2 - 1 := by
    omega
  have hEqNat : D * Y ^ 2 = 4 * R ^ 2 * (R ^ 2 - 1) :=
    Nat.cast_injective (R := ℤ) (by
      change (D : ℤ) * (Y : ℤ) ^ 2 =
        (4 : ℤ) * (R : ℤ) ^ 2 * ((R ^ 2 - 1 : ℕ) : ℤ)
      rw [hDcast, hYcast, hRcast, hRm1cast]
      exact hEqInt)
  have hNatDvd : 2 * R ∣ Y :=
    nat_two_mul_dvd_y_of_squarefree_pell_half hDsq hD0 hY0 hR0 hRm1 hEqNat
  have hIntDvd : ((2 * R : ℕ) : ℤ) ∣ a.y := by
    rcases hNatDvd with ⟨k, hk⟩
    refine ⟨k, ?_⟩
    rw [← hYcast]
    exact_mod_cast hk
  simpa [R, hRcast] using hIntDvd

omit [Fact (Squarefree d)] [Fact (d ≠ 1)] in
private theorem exists_pell_sq_of_half_and_dvd {a : Pell.Solution₁ d} {r : ℤ}
    (ha1 : 1 < a.x) (hx : a.x + 1 = 2 * r ^ 2) (hydiv : 2 * r ∣ a.y) :
    ∃ b : Pell.Solution₁ d, b ^ 2 = a := by
  rcases hydiv with ⟨s, hs⟩
  have hr0 : r ≠ 0 := by
    intro hr
    nlinarith [ha1, hx]
  have hx' : a.x = 2 * r ^ 2 - 1 := by omega
  have hy' : a.y = 2 * r * s := hs
  have hbprop : r ^ 2 - d * s ^ 2 = 1 := by
    have hprop := a.prop
    rw [hx', hy'] at hprop
    have hr2pos : 0 < r ^ 2 := sq_pos_of_ne_zero hr0
    nlinarith
  let b : Pell.Solution₁ d := Pell.Solution₁.mk r s hbprop
  refine ⟨b, ?_⟩
  apply Pell.Solution₁.ext
  · simp [b, pow_two]
    nlinarith [hbprop, hx']
  · simp [b, pow_two, hy']
    ring_nf

omit [Fact (d ≠ 1)] in
private theorem exists_pellSolution_sq_of_isSquare_two_mul_x_add_one
    {a : Pell.Solution₁ d} (ha : Pell.IsFundamental a)
    (hsq : IsSquare (Int.toNat (2 * (a.x + 1)))) :
    ∃ b : Pell.Solution₁ d, b ^ 2 = a := by
  obtain ⟨m, hm0, hm⟩ :=
    exists_int_sq_eq_of_isSquare_toNat_of_pos
      (two_mul_x_add_one_pos_of_isFundamental d ha) hsq
  obtain ⟨r, hr0, _hmr, hx⟩ := exists_half_of_nonneg_sq_eq_two_mul hm0 hm
  exact exists_pell_sq_of_half_and_dvd (d := d) (a := a) ha.1 hx
    (two_mul_dvd_y_of_pell_half d ha hr0 hx)

private theorem isAmbiguousIdeal_span_one_add_unit_of_conjAut_mul_self_eq_one
    (u : OKˣ)
    (hu :
      Units.mapEquiv (conjOK).toMulEquiv u * u = 1) :
    IsAmbiguousIdeal conjOK
      (Ideal.span ({1 + (u : OK)} : Set OK)) := by
  let K := Qsqrtd (d : ℚ)
  have hunit : conjAutRingOfIntegers K (u : OK) * (u : OK) = 1 := by
    simpa using Units.ext_iff.mp hu
  change Ideal.map (conjAutRingOfIntegers K : OK →+* OK)
      (Ideal.span ({1 + (u : OK)} : Set OK)) =
    Ideal.span ({1 + (u : OK)} : Set OK)
  rw [Ideal.map_span, Set.image_singleton]
  rw [← Ideal.span_singleton_mul_right_unit u.isUnit]
  change Ideal.span ({conjAutRingOfIntegers K (1 + (u : OK)) * (u : OK)} : Set OK) =
    Ideal.span ({1 + (u : OK)} : Set OK)
  rw [show conjAutRingOfIntegers K (1 + (u : OK)) * (u : OK) = 1 + (u : OK) by
    rw [map_add, map_one, add_mul, one_mul, hunit, add_comm]]

private theorem exists_nonzero_fullRamifiedParityVector_span_one_add_unitOfFundamentalPell
    {a : Pell.Solution₁ d} (ha : Pell.IsFundamental a) :
    let u := unitOfPellSolution d a
    ∃ J : (Ideal OK)⁰,
      (J : Ideal OK) = Ideal.span ({1 + (u : OK)} : Set OK) ∧
        ∃ p, fullRamifiedParityVector d J p ≠ 0 := by
  intro u
  have hu_ne_neg_one : u ≠ -1 := by
    simpa [u] using unitOfPellSolution_ne_neg_one_of_y_ne_zero d (ne_of_gt ha.2.1)
  let J : (Ideal OK)⁰ :=
    Ideal.spanSingletonNonzero
      (by simpa [u] using one_add_unit_ne_zero_of_ne_neg_one d u hu_ne_neg_one)
  refine ⟨J, rfl, ?_⟩
  by_contra hnone
  have hparity : ∀ p, fullRamifiedParityVector d J p = 0 := fun p => by
    by_contra hp
    exact hnone ⟨p, hp⟩
  have hJamb : IsAmbiguousIdeal conjOK (J : Ideal OK) := by
    simpa [J, u] using
      isAmbiguousIdeal_span_one_add_unit_of_conjAut_mul_self_eq_one d u
        (unitOfPellSolution_conjAut_mul_self_eq_one d a)
  have hsqNorm : IsSquare (Ideal.absNorm (J : Ideal OK)) :=
    isSquare_absNorm_of_isAmbiguousIdeal_of_forall_fullRamifiedParityVector_eq_zero
      d J hJamb hparity
  have hnorm : Ideal.absNorm (J : Ideal OK) = Int.toNat (2 * (a.x + 1)) := by
    simpa [J, u] using absNorm_span_one_add_unitOfPellSolution_of_isFundamental d ha
  have hsqTwo : IsSquare (Int.toNat (2 * (a.x + 1))) := hnorm ▸ hsqNorm
  exact (pell_isFundamental_not_sq d ha)
    (exists_pellSolution_sq_of_isSquare_two_mul_x_add_one d ha hsqTwo)

theorem exists_ambiguous_narrowPrincipal_with_nonzero_fullRamifiedParityVector_of_real
    (hd : 0 < d) :
    ∃ J : (Ideal OK)⁰,
      IsAmbiguousIdeal conjOK (J : Ideal OK) ∧
        NarrowClassGroup.mk0 J = (1 : NarrowClassGroup OK) ∧
          ∃ p, fullRamifiedParityVector d J p ≠ 0 := by
  classical
  obtain ⟨a, ha, _hu_ne_one, hu_ne_neg_one, hu⟩ := exists_fundamental_pell_unit_of_real d hd
  let u := unitOfPellSolution d a
  have hupos :
      let uK : (FractionRing OK)ˣ :=
        Units.map (algebraMap OK (FractionRing OK)).toMonoidHom u
      NarrowClassGroup.IsTotallyPositive (uK : FractionRing OK) := by
    simpa [u] using
      unitOfPellSolution_isTotallyPositive_of_pos d hd
        (show 0 < a.x from zero_lt_one.trans ha.1) ha.2.1
  obtain ⟨J, hJspan, hJparity⟩ :=
    exists_nonzero_fullRamifiedParityVector_span_one_add_unitOfFundamentalPell d ha
  have hJamb : IsAmbiguousIdeal conjOK (J : Ideal OK) := by
    rw [hJspan]
    simpa [u] using isAmbiguousIdeal_span_one_add_unit_of_conjAut_mul_self_eq_one d u hu
  have hJnarrow : NarrowClassGroup.mk0 J = (1 : NarrowClassGroup OK) := by
    let α : OK := 1 + (u : OK)
    let uK : (FractionRing OK)ˣ :=
      Units.map (algebraMap OK (FractionRing OK)).toMonoidHom u
    have hα0 : α ≠ 0 :=
      one_add_unit_ne_zero_of_ne_neg_one d u (by simpa [u] using hu_ne_neg_one)
    have hαpos : NarrowClassGroup.IsTotallyPositive
        (algebraMap OK (FractionRing OK) α) := by
      intro σ
      have huσ : 0 < σ (uK : FractionRing OK) := by
        simpa [uK] using hupos σ
      have hsum : 0 < (1 : ℝ) + σ (uK : FractionRing OK) := add_pos zero_lt_one huσ
      simpa [α, uK, map_add, RingHom.comp_apply] using hsum
    have hJ_eq_Jα : J = Ideal.spanSingletonNonzero hα0 := by
      apply Subtype.ext
      simpa [α, u] using hJspan
    rw [hJ_eq_Jα]
    exact NarrowClassGroup.mk0_span_singleton_eq_one_of_isTotallyPositive hα0 hαpos
  exact ⟨J, hJamb, hJnarrow, hJparity⟩

end Qsqrtd

end Ambiguous
end ClassGroup
end QuadraticNumberFields
