/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/

import QuadraticNumberFields.ClassGroup.GenusTheory.PrimeDiscriminant.Basic
import QNFMathlib.NumberTheory.NumberField.NarrowClassGroup
import QuadraticNumberFields.Qsqrtd.TotallyRealComplex
import QuadraticNumberFields.RingOfIntegers.Norm
import QuadraticNumberFields.Splitting.MinpolyMod

/-!
# Principal Norms And Genus Characters

This file proves that a totally positive principal generator has nonnegative
algebra norm, and that a nonnegative principal norm coprime to a signed prime
discriminant has trivial local Kronecker value.
-/

open scoped NumberField QuadraticNumberFields.Splitting

namespace QuadraticNumberFields
namespace ClassGroup
namespace GenusTheory

attribute [-instance] DivisionRing.toRatAlgebra

variable (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)]

local notation "OK" => NumberField.RingOfIntegers (Qsqrtd (d : ℚ))

/-- A totally positive algebraic integer in `𝒪(ℚ(√d))` has nonnegative
integer algebra norm. -/
theorem algebraNorm_nonneg_of_isTotallyPositive
    {α : OK}
    (hα : NarrowClassGroup.IsTotallyPositive
      (algebraMap OK (FractionRing OK) α)) :
    0 ≤ Algebra.norm ℤ α := by
  by_cases hdneg : d < 0
  · exact RingOfIntegers.algebraNorm_nonneg_of_neg d hdneg α
  have hd0 : d ≠ 0 := Squarefree.ne_zero (Fact.out : Squarefree d)
  have hdpos : 0 < d := by omega
  have hdreal : 0 ≤ (d : ℝ) := by exact_mod_cast le_of_lt hdpos
  let e : FractionRing OK ≃ₐ[OK] Qsqrtd (d : ℚ) :=
    FractionRing.algEquiv OK (Qsqrtd (d : ℚ))
  let σpos : FractionRing OK →+* ℝ :=
    (Qsqrtd.realEmbeddingPos d hdreal).toRingHom.comp e.toRingHom
  let σneg : FractionRing OK →+* ℝ :=
    (Qsqrtd.realEmbeddingNeg d hdreal).toRingHom.comp e.toRingHom
  have hpos : 0 < Qsqrtd.realEmbeddingPos d hdreal (α : Qsqrtd (d : ℚ)) := by
    simpa [σpos, e] using hα σpos
  have hneg : 0 < Qsqrtd.realEmbeddingNeg d hdreal (α : Qsqrtd (d : ℚ)) := by
    simpa [σneg, e] using hα σneg
  have hnorm_real : 0 < (Qsqrtd.norm (α : Qsqrtd (d : ℚ)) : ℝ) :=
    Qsqrtd.norm_pos_of_realEmbedding_pos d hdreal hpos hneg
  have hnorm_rat : 0 < Qsqrtd.norm (α : Qsqrtd (d : ℚ)) := by
    exact_mod_cast hnorm_real
  have hcast : (0 : ℚ) ≤ (Algebra.norm ℤ α : ℚ) := by
    rw [Algebra.coe_norm_int (K := Qsqrtd (d : ℚ)),
      Qsqrtd.algebraNorm_ratAlgebra_eq_qsqrtdNorm]
    exact hnorm_rat.le
  exact_mod_cast hcast

private theorem int_emod_two_eq_one_of_natAbs_coprime_of_two_dvd
    {m : ℤ} {N : ℕ} (hm : 0 ≤ m) (hcop : Nat.Coprime m.natAbs N)
    (h2N : 2 ∣ N) :
    m % 2 = 1 := by
  have hcop2 : Nat.Coprime m.natAbs 2 :=
    Nat.Coprime.coprime_dvd_right h2N hcop
  have hodd : Odd m.natAbs := hcop2.odd_of_right
  have habs : ((m.natAbs : ℕ) : ℤ) = m := Int.natAbs_of_nonneg hm
  have hmod : m.natAbs % 2 = 1 := Nat.odd_iff.mp hodd
  omega

private theorem sq_emod_eight_of_odd (n : ℤ) (hn : ¬ 2 ∣ n) :
    n ^ 2 % 8 = 1 := by
  have hn8 : n % 8 = 1 ∨ n % 8 = 3 ∨ n % 8 = 5 ∨ n % 8 = 7 := by
    omega
  rcases hn8 with h1 | h3 | h5 | h7
  · exact ((show n ≡ 1 [ZMOD 8] from h1).pow 2).eq
  · exact ((show n ≡ 3 [ZMOD 8] from h3).pow 2).eq
  · exact ((show n ≡ 5 [ZMOD 8] from h5).pow 2).eq
  · exact ((show n ≡ 7 [ZMOD 8] from h7).pow 2).eq

private theorem zsqrtd_norm_emod_four_eq_one_of_param_mod_four_three
    {D : ℤ} (z : Zsqrtd D) (hd4 : D % 4 = 3)
    (hnodd : Zsqrtd.norm z % 2 = 1) :
    Zsqrtd.norm z % 4 = 1 := by
  rw [RingOfIntegers.norm_zsqrtd]
  by_cases ha2 : 2 ∣ z.re
  · have ha4 : z.re ^ 2 ≡ 0 [ZMOD 4] := Int.sq_emod_four_of_even z.re ha2
    by_cases hb2 : 2 ∣ z.im
    · have hb4 : z.im ^ 2 ≡ 0 [ZMOD 4] := Int.sq_emod_four_of_even z.im hb2
      have hnorm4 : z.re ^ 2 - D * z.im ^ 2 ≡ 0 [ZMOD 4] := by
        simpa using ha4.sub ((Int.ModEq.refl D).mul hb4)
      have hnorm2 : (z.re ^ 2 - D * z.im ^ 2) % 2 = 0 := by
        simpa using (hnorm4.of_dvd (by norm_num : (2 : ℤ) ∣ 4)).eq
      rw [RingOfIntegers.norm_zsqrtd] at hnodd
      omega
    · have hb4 : z.im ^ 2 ≡ 1 [ZMOD 4] := Int.sq_emod_four_of_odd z.im hb2
      calc
        z.re ^ 2 - D * z.im ^ 2 ≡ 0 - 3 * 1 [ZMOD 4] :=
          ha4.sub ((show D ≡ 3 [ZMOD 4] from hd4).mul hb4)
        _ ≡ 1 [ZMOD 4] := by decide +revert
  · have ha4 : z.re ^ 2 ≡ 1 [ZMOD 4] := Int.sq_emod_four_of_odd z.re ha2
    by_cases hb2 : 2 ∣ z.im
    · have hb4 : z.im ^ 2 ≡ 0 [ZMOD 4] := Int.sq_emod_four_of_even z.im hb2
      simpa using ha4.sub ((Int.ModEq.refl D).mul hb4)
    · have hb4 : z.im ^ 2 ≡ 1 [ZMOD 4] := Int.sq_emod_four_of_odd z.im hb2
      have hnorm4 : z.re ^ 2 - D * z.im ^ 2 ≡ 2 [ZMOD 4] :=
        (ha4.sub ((show D ≡ 3 [ZMOD 4] from hd4).mul hb4)).trans (by decide)
      have hnorm2 : (z.re ^ 2 - D * z.im ^ 2) % 2 = 0 := by
        simpa using (hnorm4.of_dvd (by norm_num : (2 : ℤ) ∣ 4)).eq
      rw [RingOfIntegers.norm_zsqrtd] at hnodd
      omega

private theorem zsqrtd_norm_emod_eight_eq_one_or_one_sub_param_of_param_even
    {D : ℤ} (z : Zsqrtd D) (hd2 : D % 2 = 0)
    (hnodd : Zsqrtd.norm z % 2 = 1) :
    Zsqrtd.norm z % 8 = 1 ∨ Zsqrtd.norm z % 8 = (1 - D) % 8 := by
  rw [RingOfIntegers.norm_zsqrtd]
  by_cases ha2 : 2 ∣ z.re
  · have ha4 : z.re ^ 2 ≡ 0 [ZMOD 4] := Int.sq_emod_four_of_even z.re ha2
    have hnorm2 : (z.re ^ 2 - D * z.im ^ 2) % 2 = 0 := by
      have ha2mod := ha4.of_dvd (by norm_num : (2 : ℤ) ∣ 4)
      have hprod2 : D * z.im ^ 2 ≡ 0 [ZMOD 2] := by
        simpa using (show D ≡ 0 [ZMOD 2] from hd2).mul (Int.ModEq.refl (z.im ^ 2))
      simpa using (ha2mod.sub hprod2).eq
    rw [RingOfIntegers.norm_zsqrtd] at hnodd
    omega
  · have ha8 : z.re ^ 2 ≡ 1 [ZMOD 8] :=
      sq_emod_eight_of_odd z.re ha2
    by_cases hb2 : 2 ∣ z.im
    · have hb4 : z.im ^ 2 ≡ 0 [ZMOD 4] := Int.sq_emod_four_of_even z.im hb2
      have h2b : (2 : ℤ) * z.im ^ 2 ≡ 0 [ZMOD 8] := by
        simpa using hb4.mul_left' (c := (2 : ℤ))
      obtain ⟨c, hc⟩ := Int.dvd_of_emod_eq_zero hd2
      have hDb : D * z.im ^ 2 ≡ 0 [ZMOD 8] := by
        calc
          D * z.im ^ 2 = (2 * c) * z.im ^ 2 := congrArg (fun x : ℤ ↦ x * z.im ^ 2) hc
          _ = c * (2 * z.im ^ 2) := by ring
          _ ≡ c * 0 [ZMOD 8] := (Int.ModEq.refl c).mul h2b
          _ = 0 := by ring
      left
      simpa using ha8.sub hDb
    · have hb8 : z.im ^ 2 ≡ 1 [ZMOD 8] :=
        sq_emod_eight_of_odd z.im hb2
      right
      simpa only [mul_one] using (ha8.sub ((Int.ModEq.refl D).mul hb8)).eq

private theorem zsqrtd_norm_emod_eight_eq_one_or_seven_of_param_mod_eight_two
    {D : ℤ} (z : Zsqrtd D) (hd8 : D % 8 = 2)
    (hnodd : Zsqrtd.norm z % 2 = 1) :
    Zsqrtd.norm z % 8 = 1 ∨ Zsqrtd.norm z % 8 = 7 := by
  rcases zsqrtd_norm_emod_eight_eq_one_or_one_sub_param_of_param_even z (by omega) hnodd
    with h | h
  · exact Or.inl h
  · exact Or.inr (by omega)

private theorem zsqrtd_norm_emod_eight_eq_one_or_three_of_param_mod_eight_six
    {D : ℤ} (z : Zsqrtd D) (hd8 : D % 8 = 6)
    (hnodd : Zsqrtd.norm z % 2 = 1) :
    Zsqrtd.norm z % 8 = 1 ∨ Zsqrtd.norm z % 8 = 3 := by
  rcases zsqrtd_norm_emod_eight_eq_one_or_one_sub_param_of_param_even z (by omega) hnodd
    with h | h
  · exact Or.inl h
  · exact Or.inr (by omega)

private theorem kroneckerSymNat_twoPrimeDiscriminantFactor_zsqrtd_norm_eq_one
    {D : ℤ} [Fact (Squarefree D)]
    (z : Zsqrtd D) (hd4 : D % 4 ≠ 1) (hN : 0 ≤ Zsqrtd.norm z)
    (hcop : Nat.Coprime (Zsqrtd.norm z).natAbs
      (twoPrimeDiscriminantFactor D).natAbs) :
    kroneckerSymNat (twoPrimeDiscriminantFactor D) (Zsqrtd.norm z).natAbs = 1 := by
  refine kroneckerSymNat_twoPrimeDiscriminantFactor_eq_one_of_mod_conditions ?_ ?_ ?_
  · intro hd2
    have hcop4 : Nat.Coprime (Zsqrtd.norm z).natAbs 4 := by
      simpa [twoPrimeDiscriminantFactor, hd2] using hcop
    have hnodd : Zsqrtd.norm z % 2 = 1 :=
      int_emod_two_eq_one_of_natAbs_coprime_of_two_dvd hN hcop4 (by norm_num)
    have hmod :=
      zsqrtd_norm_emod_four_eq_one_of_param_mod_four_three z (by omega) hnodd
    have habs := Int.natAbs_of_nonneg hN
    omega
  · intro hd2 hd8
    have hcop8 : Nat.Coprime (Zsqrtd.norm z).natAbs 8 := by
      simpa [twoPrimeDiscriminantFactor, hd2, hd8] using hcop
    have hnodd : Zsqrtd.norm z % 2 = 1 :=
      int_emod_two_eq_one_of_natAbs_coprime_of_two_dvd hN hcop8 (by norm_num)
    rcases zsqrtd_norm_emod_eight_eq_one_or_seven_of_param_mod_eight_two z hd8 hnodd
      with hmod | hmod
    · left
      have habs := Int.natAbs_of_nonneg hN
      omega
    · right
      have habs := Int.natAbs_of_nonneg hN
      omega
  · intro hd2 hd8
    have hcop8 : Nat.Coprime (Zsqrtd.norm z).natAbs 8 := by
      simpa [twoPrimeDiscriminantFactor, hd2, hd8] using hcop
    have hnodd : Zsqrtd.norm z % 2 = 1 :=
      int_emod_two_eq_one_of_natAbs_coprime_of_two_dvd hN hcop8 (by norm_num)
    have hd4_ne_zero : D % 4 ≠ 0 := by
      intro hd40
      exact squarefree_int_not_dvd_four D (Fact.out : Squarefree D)
        (Int.dvd_of_emod_eq_zero hd40)
    have hd86 : D % 8 = 6 := by omega
    rcases zsqrtd_norm_emod_eight_eq_one_or_three_of_param_mod_eight_six z hd86 hnodd
      with hmod | hmod
    · left
      have habs := Int.natAbs_of_nonneg hN
      omega
    · right
      have habs := Int.natAbs_of_nonneg hN
      omega

private theorem legendreSym_zsqrtd_norm_eq_one_of_dvd_param
    {D : ℤ} {p : ℕ} [Fact p.Prime] (hpd : (p : ℤ) ∣ D)
    (z : Zsqrtd D) (hz : ¬ (p : ℤ) ∣ Zsqrtd.norm z) :
    legendreSym p (Zsqrtd.norm z) = 1 := by
  have hnorm : ((Zsqrtd.norm z : ℤ) : ZMod p) ≠ 0 := by
    intro hzero
    exact hz ((ZMod.intCast_zmod_eq_zero_iff_dvd (Zsqrtd.norm z) p).mp hzero)
  refine (legendreSym.eq_one_iff p hnorm).mpr ⟨(z.re : ZMod p), ?_⟩
  have hD : ((D : ℤ) : ZMod p) = 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd D p).mpr hpd
  rw [RingOfIntegers.norm_zsqrtd]
  push_cast
  rw [hD]
  ring

private theorem legendreSym_zOnePlusSqrtOverTwo_norm_eq_one_of_dvd_discr
    {k : ℤ} {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    (hpd : (p : ℤ) ∣ 1 + 4 * k) (z : ZOnePlusSqrtdOverTwo k)
    (hz : ¬ (p : ℤ) ∣ QuadraticAlgebra.norm z) :
    legendreSym p (QuadraticAlgebra.norm z) = 1 := by
  have hnorm : ((QuadraticAlgebra.norm z : ℤ) : ZMod p) ≠ 0 := by
    intro hzero
    exact hz ((ZMod.intCast_zmod_eq_zero_iff_dvd (QuadraticAlgebra.norm z) p).mp hzero)
  refine (legendreSym.eq_one_iff p hnorm).mpr ?_
  let w : ZMod p := 2 * (z.re : ZMod p) + (z.im : ZMod p)
  refine ⟨(2 : ZMod p)⁻¹ * w, ?_⟩
  have h2 : (2 : ZMod p) ≠ 0 := Splitting.zmod_two_ne_zero_of_prime_ne_two p hp2
  have hD : (1 : ZMod p) + 4 * (k : ZMod p) = 0 := by
    simpa using (ZMod.intCast_zmod_eq_zero_iff_dvd (1 + 4 * k) p).mpr hpd
  have hk : (k : ZMod p) * 4 = -1 := by linear_combination hD
  rw [RingOfIntegers.norm_zOnePlusSqrtOverTwo]
  push_cast
  field_simp [w, h2]
  ring_nf
  rw [show (z.im : ZMod p) ^ 2 * (k : ZMod p) * 4 =
      ((k : ZMod p) * 4) * (z.im : ZMod p) ^ 2 by ring, hk]
  ring

private theorem kroneckerSymNat_primeDiscriminantFactor_zsqrtd_norm_eq_one
    {D : ℤ} [Fact (Squarefree D)] [Fact (D ≠ 1)]
    (p : RamifiedPrimeIndex D) (z : Zsqrtd D) (hd4 : D % 4 ≠ 1)
    (hN : 0 ≤ Zsqrtd.norm z)
    (hcop : Nat.Coprime (Zsqrtd.norm z).natAbs
      (primeDiscriminantFactor D p).natAbs) :
    kroneckerSymNat (primeDiscriminantFactor D p) (Zsqrtd.norm z).natAbs = 1 := by
  by_cases hp2 : p.1 = 2
  · rw [primeDiscriminantFactor_of_val_eq_two D p hp2] at hcop ⊢
    exact kroneckerSymNat_twoPrimeDiscriminantFactor_zsqrtd_norm_eq_one
      z hd4 hN hcop
  · rw [primeDiscriminantFactor_of_val_ne_two D p hp2] at hcop ⊢
    letI : Fact p.1.Prime := ⟨prime_of_mem_ramifiedPrimeIndex D p⟩
    rw [kroneckerSymNat_oddPrimeDiscriminantFactor_eq_legendreSym hp2]
    have hcop_p : Nat.Coprime (Zsqrtd.norm z).natAbs p.1 := by
      simpa using hcop
    have hnvd_nat : ¬ p.1 ∣ (Zsqrtd.norm z).natAbs :=
      ((Fact.out : p.1.Prime).coprime_iff_not_dvd).mp hcop_p.symm
    have hnvd : ¬ (p.1 : ℤ) ∣ Zsqrtd.norm z :=
      fun h ↦ hnvd_nat (Int.natCast_dvd.mp h)
    rw [Int.natAbs_of_nonneg hN]
    exact legendreSym_zsqrtd_norm_eq_one_of_dvd_param
      (dvd_parameter_of_mem_ramifiedPrimeIndex_of_ne_two D p hp2) z hnvd

private theorem kroneckerSymNat_primeDiscriminantFactor_halfIntegral_norm_eq_one
    {D k : ℤ} [Fact (Squarefree D)] [Fact (D ≠ 1)]
    (p : RamifiedPrimeIndex D) (z : ZOnePlusSqrtdOverTwo k)
    (hk : D = 1 + 4 * k) (hN : 0 ≤ QuadraticAlgebra.norm z)
    (hcop : Nat.Coprime (QuadraticAlgebra.norm z).natAbs
      (primeDiscriminantFactor D p).natAbs) :
    kroneckerSymNat (primeDiscriminantFactor D p)
      (QuadraticAlgebra.norm z).natAbs = 1 := by
  have hd4 : D % 4 = 1 := by omega
  have hp2 : p.1 ≠ 2 :=
    ne_two_of_mem_ramifiedPrimeIndex_of_mod_four_eq_one D p hd4
  rw [primeDiscriminantFactor_of_val_ne_two D p hp2] at hcop ⊢
  letI : Fact p.1.Prime := ⟨prime_of_mem_ramifiedPrimeIndex D p⟩
  rw [kroneckerSymNat_oddPrimeDiscriminantFactor_eq_legendreSym hp2]
  have hcop_p : Nat.Coprime (QuadraticAlgebra.norm z).natAbs p.1 := by
    simpa using hcop
  have hnvd_nat : ¬ p.1 ∣ (QuadraticAlgebra.norm z).natAbs :=
    ((Fact.out : p.1.Prime).coprime_iff_not_dvd).mp hcop_p.symm
  have hnvd : ¬ (p.1 : ℤ) ∣ QuadraticAlgebra.norm z :=
    fun h ↦ hnvd_nat (Int.natCast_dvd.mp h)
  rw [Int.natAbs_of_nonneg hN]
  exact legendreSym_zOnePlusSqrtOverTwo_norm_eq_one_of_dvd_discr hp2
    (by simpa [hk] using dvd_parameter_of_mem_ramifiedPrimeIndex_of_ne_two D p hp2)
    z hnvd

/-- A principal ideal generated by an element with nonnegative algebra norm has
trivial local Kronecker value whenever its absolute norm is coprime to the
corresponding signed prime discriminant. -/
theorem kroneckerSymNat_primeDiscriminantFactor_absNorm_span_eq_one
    (p : RamifiedPrimeIndex d) {α : OK}
    (hN : 0 ≤ Algebra.norm ℤ α)
    (hcop : Nat.Coprime (Ideal.absNorm (Ideal.span ({α} : Set OK)))
      (primeDiscriminantFactor d p).natAbs) :
    kroneckerSymNat (primeDiscriminantFactor d p)
      (Ideal.absNorm (Ideal.span ({α} : Set OK))) = 1 := by
  by_cases hd4 : d % 4 = 1
  · obtain ⟨k, hk⟩ := RingOfIntegers.exists_k_of_mod_four_eq_one hd4
    let z : ZOnePlusSqrtdOverTwo k :=
      (RingOfIntegers.ringOfIntegers_equiv_zOnePlusSqrtOverTwo_of_eq d k hk) α
    have hnorm : Algebra.norm ℤ α = QuadraticAlgebra.norm z := by
      simpa [z] using RingOfIntegers.algebraNorm_eq_zOnePlusSqrtOverTwo_norm_of_eq
        (d := d) k hk α
    rw [Ideal.absNorm_span_singleton, hnorm] at hcop ⊢
    exact kroneckerSymNat_primeDiscriminantFactor_halfIntegral_norm_eq_one
      p z hk (by simpa [hnorm] using hN) hcop
  · let z : Zsqrtd d :=
      (RingOfIntegers.ringOfIntegers_equiv_zsqrtd_of_mod_four_ne_one d hd4) α
    have hnorm : Algebra.norm ℤ α = Zsqrtd.norm z := by
      simpa [z] using RingOfIntegers.algebraNorm_eq_zsqrtd_norm_of_mod_four_ne_one
        (d := d) hd4 α
    rw [Ideal.absNorm_span_singleton, hnorm] at hcop ⊢
    exact kroneckerSymNat_primeDiscriminantFactor_zsqrtd_norm_eq_one
      p z hd4 (by simpa [hnorm] using hN) hcop

end GenusTheory
end ClassGroup
end QuadraticNumberFields
