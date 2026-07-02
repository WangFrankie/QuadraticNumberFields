/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/

import QuadraticNumberFields.ClassGroup.GenusTheory.Characters.Basic
import QuadraticNumberFields.Qsqrtd.TotallyRealComplex
import QuadraticNumberFields.RingOfIntegers.Norm
import QNFMathlib.NumberTheory.LegendreSymbol.KroneckerSymbolPeriodicity
import QNFMathlib.RingTheory.ClassGroup
import QNFMathlib.RingTheory.Ideal.Norm.AbsNorm
import QuadraticNumberFields.Splitting.Qsqrtd.Kronecker
/-!
# Genus Characters

This file proves the local norm/Kronecker facts and well-definedness needed to
descend the raw signed-factor genus characters from `Characters.Basic`, and
packages the final genus-character map.
-/

namespace QuadraticNumberFields
namespace ClassGroup
namespace GenusTheory

open scoped NumberField nonZeroDivisors QuadraticNumberFields.ClassGroup

attribute [-instance] DivisionRing.toRatAlgebra

variable (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)]

/-- Clear denominators in a principal fractional multiplier relating two
signed-factor-coprime ideal representatives. -/
private theorem exists_integral_multipliers_of_mul_toPrincipalIdeal_eq
      (q : {q // q ∈ signedPrimeDiscriminantFactors d})
      (I J : signedFactorCoprimeIdealSubmonoid d q)
      {x : (FractionRing (NumberField.RingOfIntegers (Qsqrtd (d : ℚ))))ˣ}
      (hJ : FractionalIdeal.mk0
          (FractionRing (NumberField.RingOfIntegers (Qsqrtd (d : ℚ))))
          (signedFactorCoprimeIdealNonzeroMonoidHom d q I) *
        toPrincipalIdeal (NumberField.RingOfIntegers (Qsqrtd (d : ℚ)))
          (FractionRing (NumberField.RingOfIntegers (Qsqrtd (d : ℚ)))) x =
        FractionalIdeal.mk0
          (FractionRing (NumberField.RingOfIntegers (Qsqrtd (d : ℚ))))
          (signedFactorCoprimeIdealNonzeroMonoidHom d q J)) :
      ∃ a b : NumberField.RingOfIntegers (Qsqrtd (d : ℚ)), b ≠ 0 ∧
        Ideal.span ({a} : Set (NumberField.RingOfIntegers (Qsqrtd (d : ℚ)))) *
            (I : Ideal (NumberField.RingOfIntegers (Qsqrtd (d : ℚ)))) =
          Ideal.span ({b} : Set (NumberField.RingOfIntegers (Qsqrtd (d : ℚ)))) *
            (J : Ideal (NumberField.RingOfIntegers (Qsqrtd (d : ℚ)))) := by
  have hfrac : FractionalIdeal.spanSingleton
        (nonZeroDivisors (NumberField.RingOfIntegers (Qsqrtd (d : ℚ))))
        (x : FractionRing (NumberField.RingOfIntegers (Qsqrtd (d : ℚ)))) *
        ((signedFactorCoprimeIdealNonzeroMonoidHom d q I :
          Ideal (NumberField.RingOfIntegers (Qsqrtd (d : ℚ)))) :
          FractionalIdeal
            (nonZeroDivisors (NumberField.RingOfIntegers (Qsqrtd (d : ℚ))))
            (FractionRing (NumberField.RingOfIntegers (Qsqrtd (d : ℚ))))) =
      ((signedFactorCoprimeIdealNonzeroMonoidHom d q J :
          Ideal (NumberField.RingOfIntegers (Qsqrtd (d : ℚ)))) :
          FractionalIdeal
            (nonZeroDivisors (NumberField.RingOfIntegers (Qsqrtd (d : ℚ))))
            (FractionRing (NumberField.RingOfIntegers (Qsqrtd (d : ℚ))))) := by
    have hJ_val := congrArg
      (fun U : (FractionalIdeal
          (nonZeroDivisors (NumberField.RingOfIntegers (Qsqrtd (d : ℚ))))
          (FractionRing (NumberField.RingOfIntegers (Qsqrtd (d : ℚ)))))ˣ =>
          (U : FractionalIdeal
            (nonZeroDivisors (NumberField.RingOfIntegers (Qsqrtd (d : ℚ))))
            (FractionRing (NumberField.RingOfIntegers (Qsqrtd (d : ℚ)))))) hJ
    simpa [coe_toPrincipalIdeal, mul_comm] using hJ_val
  simpa using
    (FractionalIdeal.exists_span_mul_eq_span_mul_of_spanSingleton_mul_coeIdeal_eq_coeIdeal
      (R := NumberField.RingOfIntegers (Qsqrtd (d : ℚ))) hfrac)

/-- Clear denominators in a principal fractional multiplier while retaining the
fraction-field element represented by the numerator and denominator. -/
private theorem exists_integral_multipliers_with_mk'_of_mul_toPrincipalIdeal_eq
      (q : {q // q ∈ signedPrimeDiscriminantFactors d})
      (I J : signedFactorCoprimeIdealSubmonoid d q)
      {x : (FractionRing (NumberField.RingOfIntegers (Qsqrtd (d : ℚ))))ˣ}
      (hJ : FractionalIdeal.mk0
          (FractionRing (NumberField.RingOfIntegers (Qsqrtd (d : ℚ))))
          (signedFactorCoprimeIdealNonzeroMonoidHom d q I) *
        toPrincipalIdeal (NumberField.RingOfIntegers (Qsqrtd (d : ℚ)))
          (FractionRing (NumberField.RingOfIntegers (Qsqrtd (d : ℚ)))) x =
        FractionalIdeal.mk0
          (FractionRing (NumberField.RingOfIntegers (Qsqrtd (d : ℚ))))
          (signedFactorCoprimeIdealNonzeroMonoidHom d q J)) :
      ∃ a b : NumberField.RingOfIntegers (Qsqrtd (d : ℚ)), ∃ hb : b ≠ 0,
        IsLocalization.mk'
            (FractionRing (NumberField.RingOfIntegers (Qsqrtd (d : ℚ)))) a
            ⟨b, mem_nonZeroDivisors_iff_ne_zero.mpr hb⟩ =
          (x : FractionRing (NumberField.RingOfIntegers (Qsqrtd (d : ℚ)))) ∧
        Ideal.span ({a} : Set (NumberField.RingOfIntegers (Qsqrtd (d : ℚ)))) *
            (I : Ideal (NumberField.RingOfIntegers (Qsqrtd (d : ℚ)))) =
          Ideal.span ({b} : Set (NumberField.RingOfIntegers (Qsqrtd (d : ℚ)))) *
            (J : Ideal (NumberField.RingOfIntegers (Qsqrtd (d : ℚ)))) := by
  have hfrac : FractionalIdeal.spanSingleton
        (nonZeroDivisors (NumberField.RingOfIntegers (Qsqrtd (d : ℚ))))
        (x : FractionRing (NumberField.RingOfIntegers (Qsqrtd (d : ℚ)))) *
        ((signedFactorCoprimeIdealNonzeroMonoidHom d q I :
          Ideal (NumberField.RingOfIntegers (Qsqrtd (d : ℚ)))) :
          FractionalIdeal
            (nonZeroDivisors (NumberField.RingOfIntegers (Qsqrtd (d : ℚ))))
            (FractionRing (NumberField.RingOfIntegers (Qsqrtd (d : ℚ))))) =
      ((signedFactorCoprimeIdealNonzeroMonoidHom d q J :
          Ideal (NumberField.RingOfIntegers (Qsqrtd (d : ℚ)))) :
          FractionalIdeal
            (nonZeroDivisors (NumberField.RingOfIntegers (Qsqrtd (d : ℚ))))
            (FractionRing (NumberField.RingOfIntegers (Qsqrtd (d : ℚ))))) := by
    have hJ_val := congrArg
      (fun U : (FractionalIdeal
          (nonZeroDivisors (NumberField.RingOfIntegers (Qsqrtd (d : ℚ))))
          (FractionRing (NumberField.RingOfIntegers (Qsqrtd (d : ℚ)))))ˣ =>
          (U : FractionalIdeal
            (nonZeroDivisors (NumberField.RingOfIntegers (Qsqrtd (d : ℚ))))
            (FractionRing (NumberField.RingOfIntegers (Qsqrtd (d : ℚ)))))) hJ
    simpa [coe_toPrincipalIdeal, mul_comm] using hJ_val
  rcases
    FractionalIdeal.exists_mk'_span_mul_eq_span_mul_of_spanSingleton_mul_coeIdeal_eq_coeIdeal
      (R := NumberField.RingOfIntegers (Qsqrtd (d : ℚ))) hfrac with
    ⟨a, b, hxb, hclear⟩
  refine ⟨a, b, mem_nonZeroDivisors_iff_ne_zero.mp b.property, ?_, hclear⟩
  simpa using hxb

/-- Clear denominators in a chosen `mk'` representative of a principal fractional
multiplier relating two signed-factor-coprime integral ideals. -/
theorem span_mul_eq_span_mul_of_mk'_eq_of_mul_toPrincipalIdeal_eq
      (q : {q // q ∈ signedPrimeDiscriminantFactors d})
      (I J : signedFactorCoprimeIdealSubmonoid d q)
      {x : (FractionRing (NumberField.RingOfIntegers (Qsqrtd (d : ℚ))))ˣ}
      (hJ : FractionalIdeal.mk0
          (FractionRing (NumberField.RingOfIntegers (Qsqrtd (d : ℚ))))
          (signedFactorCoprimeIdealNonzeroMonoidHom d q I) *
        toPrincipalIdeal (NumberField.RingOfIntegers (Qsqrtd (d : ℚ)))
          (FractionRing (NumberField.RingOfIntegers (Qsqrtd (d : ℚ)))) x =
        FractionalIdeal.mk0
          (FractionRing (NumberField.RingOfIntegers (Qsqrtd (d : ℚ))))
          (signedFactorCoprimeIdealNonzeroMonoidHom d q J))
      {a b : NumberField.RingOfIntegers (Qsqrtd (d : ℚ))}
      (hb : b ≠ 0)
      (hmk : IsLocalization.mk'
          (FractionRing (NumberField.RingOfIntegers (Qsqrtd (d : ℚ)))) a
          ⟨b, mem_nonZeroDivisors_iff_ne_zero.mpr hb⟩ =
        (x : FractionRing (NumberField.RingOfIntegers (Qsqrtd (d : ℚ))))) :
      Ideal.span ({a} : Set (NumberField.RingOfIntegers (Qsqrtd (d : ℚ)))) *
          (I : Ideal (NumberField.RingOfIntegers (Qsqrtd (d : ℚ)))) =
        Ideal.span ({b} : Set (NumberField.RingOfIntegers (Qsqrtd (d : ℚ)))) *
          (J : Ideal (NumberField.RingOfIntegers (Qsqrtd (d : ℚ)))) := by
  have hfrac : FractionalIdeal.spanSingleton
        (nonZeroDivisors (NumberField.RingOfIntegers (Qsqrtd (d : ℚ))))
        (x : FractionRing (NumberField.RingOfIntegers (Qsqrtd (d : ℚ)))) *
        ((signedFactorCoprimeIdealNonzeroMonoidHom d q I :
          Ideal (NumberField.RingOfIntegers (Qsqrtd (d : ℚ)))) :
          FractionalIdeal
            (nonZeroDivisors (NumberField.RingOfIntegers (Qsqrtd (d : ℚ))))
            (FractionRing (NumberField.RingOfIntegers (Qsqrtd (d : ℚ))))) =
      ((signedFactorCoprimeIdealNonzeroMonoidHom d q J :
          Ideal (NumberField.RingOfIntegers (Qsqrtd (d : ℚ)))) :
          FractionalIdeal
            (nonZeroDivisors (NumberField.RingOfIntegers (Qsqrtd (d : ℚ))))
            (FractionRing (NumberField.RingOfIntegers (Qsqrtd (d : ℚ))))) := by
    have hJ_val := congrArg
      (fun U : (FractionalIdeal
          (nonZeroDivisors (NumberField.RingOfIntegers (Qsqrtd (d : ℚ))))
          (FractionRing (NumberField.RingOfIntegers (Qsqrtd (d : ℚ)))))ˣ =>
          (U : FractionalIdeal
            (nonZeroDivisors (NumberField.RingOfIntegers (Qsqrtd (d : ℚ))))
            (FractionRing (NumberField.RingOfIntegers (Qsqrtd (d : ℚ)))))) hJ
    simpa [coe_toPrincipalIdeal, mul_comm] using hJ_val
  exact (FractionalIdeal.mk'_mul_coeIdeal_eq_coeIdeal
    (FractionRing (NumberField.RingOfIntegers (Qsqrtd (d : ℚ))))
    (mem_nonZeroDivisors_iff_ne_zero.mpr hb)).mp (by
      rw [hmk]
      simpa using hfrac)

/-- Clear denominators in a square principal fractional multiplier relating two
signed-factor-coprime ideal representatives. -/
private theorem exists_integral_square_multipliers_of_mul_toPrincipalIdeal_sq_eq
      (q : {q // q ∈ signedPrimeDiscriminantFactors d})
      (I J : signedFactorCoprimeIdealSubmonoid d q)
      {x : FractionRing (NumberField.RingOfIntegers (Qsqrtd (d : ℚ)))} (hx : x ≠ 0)
      (hJ : FractionalIdeal.mk0
          (FractionRing (NumberField.RingOfIntegers (Qsqrtd (d : ℚ))))
          (signedFactorCoprimeIdealNonzeroMonoidHom d q I) *
        toPrincipalIdeal (NumberField.RingOfIntegers (Qsqrtd (d : ℚ)))
          (FractionRing (NumberField.RingOfIntegers (Qsqrtd (d : ℚ))))
          (Units.mk0 (x ^ 2) (pow_ne_zero 2 hx)) =
        FractionalIdeal.mk0
          (FractionRing (NumberField.RingOfIntegers (Qsqrtd (d : ℚ))))
          (signedFactorCoprimeIdealNonzeroMonoidHom d q J)) :
      ∃ a b : NumberField.RingOfIntegers (Qsqrtd (d : ℚ)), a ≠ 0 ∧ b ≠ 0 ∧
        Ideal.span ({a} : Set (NumberField.RingOfIntegers (Qsqrtd (d : ℚ)))) *
            Ideal.span ({a} : Set (NumberField.RingOfIntegers (Qsqrtd (d : ℚ)))) *
            (I : Ideal (NumberField.RingOfIntegers (Qsqrtd (d : ℚ)))) =
          Ideal.span ({b} : Set (NumberField.RingOfIntegers (Qsqrtd (d : ℚ)))) *
            Ideal.span ({b} : Set (NumberField.RingOfIntegers (Qsqrtd (d : ℚ)))) *
            (J : Ideal (NumberField.RingOfIntegers (Qsqrtd (d : ℚ)))) := by
  have hfrac : FractionalIdeal.spanSingleton
        (nonZeroDivisors (NumberField.RingOfIntegers (Qsqrtd (d : ℚ)))) (x ^ 2) *
        ((signedFactorCoprimeIdealNonzeroMonoidHom d q I :
          Ideal (NumberField.RingOfIntegers (Qsqrtd (d : ℚ)))) :
          FractionalIdeal
            (nonZeroDivisors (NumberField.RingOfIntegers (Qsqrtd (d : ℚ))))
            (FractionRing (NumberField.RingOfIntegers (Qsqrtd (d : ℚ))))) =
      ((signedFactorCoprimeIdealNonzeroMonoidHom d q J :
          Ideal (NumberField.RingOfIntegers (Qsqrtd (d : ℚ)))) :
          FractionalIdeal
            (nonZeroDivisors (NumberField.RingOfIntegers (Qsqrtd (d : ℚ))))
            (FractionRing (NumberField.RingOfIntegers (Qsqrtd (d : ℚ))))) := by
    have hJ_val := congrArg
      (fun U : (FractionalIdeal
          (nonZeroDivisors (NumberField.RingOfIntegers (Qsqrtd (d : ℚ))))
          (FractionRing (NumberField.RingOfIntegers (Qsqrtd (d : ℚ)))))ˣ =>
          (U : FractionalIdeal
            (nonZeroDivisors (NumberField.RingOfIntegers (Qsqrtd (d : ℚ))))
            (FractionRing (NumberField.RingOfIntegers (Qsqrtd (d : ℚ)))))) hJ
    simpa [coe_toPrincipalIdeal, mul_comm] using hJ_val
  simpa using
    (FractionalIdeal.exists_span_mul_span_mul_eq_of_spanSingleton_sq_mul_coeIdeal_eq_coeIdeal
      (R := NumberField.RingOfIntegers (Qsqrtd (d : ℚ))) hx hfrac)

/-- Equality in the restricted narrow class-group map is equality after
multiplication by a totally positive principal fractional ideal. -/
theorem narrowMk0OnSignedFactorCoprimeIdeals_eq_iff_exists_fraction_ring
      (q : {q // q ∈ signedPrimeDiscriminantFactors d})
      (I J : signedFactorCoprimeIdealSubmonoid d q) :
      narrowMk0OnSignedFactorCoprimeIdeals d q I =
          narrowMk0OnSignedFactorCoprimeIdeals d q J ↔
        ∃ x : (FractionRing (NumberField.RingOfIntegers (Qsqrtd (d : ℚ))))ˣ,
          NarrowClassGroup.IsTotallyPositive
              (x : FractionRing (NumberField.RingOfIntegers (Qsqrtd (d : ℚ)))) ∧
            FractionalIdeal.mk0
                (FractionRing (NumberField.RingOfIntegers (Qsqrtd (d : ℚ))))
                (signedFactorCoprimeIdealNonzeroMonoidHom d q I) *
              toPrincipalIdeal (NumberField.RingOfIntegers (Qsqrtd (d : ℚ)))
                (FractionRing (NumberField.RingOfIntegers (Qsqrtd (d : ℚ)))) x =
                FractionalIdeal.mk0
                  (FractionRing (NumberField.RingOfIntegers (Qsqrtd (d : ℚ))))
                  (signedFactorCoprimeIdealNonzeroMonoidHom d q J) := by
  simpa [narrowMk0OnSignedFactorCoprimeIdeals] using
    (NarrowClassGroup.mk0_eq_mk0_iff_exists_fraction_ring
      (I := signedFactorCoprimeIdealNonzeroMonoidHom d q I)
      (J := signedFactorCoprimeIdealNonzeroMonoidHom d q J))

private theorem int_emod_two_eq_one_of_natAbs_coprime_of_two_dvd
    {m : ℤ} {N : ℕ} (hm : 0 ≤ m) (hcop : Nat.Coprime m.natAbs N)
    (h2N : 2 ∣ N) :
    m % 2 = 1 := by
  have hcop2 : Nat.Coprime m.natAbs 2 :=
    Nat.Coprime.coprime_dvd_right h2N hcop
  have hnot_two : ¬ 2 ∣ m.natAbs :=
    (Nat.prime_two.coprime_iff_not_dvd).mp hcop2.symm
  have hnat : m.natAbs % 2 = 1 := by omega
  have habs : ((m.natAbs : ℕ) : ℤ) = m := Int.natAbs_of_nonneg hm
  omega

private theorem sq_emod_eight_of_odd (n : ℤ) (hn : ¬ 2 ∣ n) :
    n ^ 2 % 8 = 1 := by
  have hn2 : n % 2 = 1 := by omega
  have hn8 : n % 8 = 1 ∨ n % 8 = 3 ∨ n % 8 = 5 ∨ n % 8 = 7 := by omega
  rcases hn8 with h1 | h3 | h5 | h7
  · have hmod : n ≡ 1 [ZMOD 8] := by exact h1
    simpa using (hmod.pow 2).eq
  · have hmod : n ≡ 3 [ZMOD 8] := by exact h3
    simpa using (hmod.pow 2).eq
  · have hmod : n ≡ 5 [ZMOD 8] := by exact h5
    simpa using (hmod.pow 2).eq
  · have hmod : n ≡ 7 [ZMOD 8] := by exact h7
    simpa using (hmod.pow 2).eq

private theorem zsqrtd_norm_emod_four_eq_one_of_param_mod_four_three
    {D : ℤ} (z : Zsqrtd D) (hd4 : D % 4 = 3)
    (hnodd : (Zsqrtd.norm z) % 2 = 1) :
    Zsqrtd.norm z % 4 = 1 := by
  rw [RingOfIntegers.norm_zsqrtd]
  by_cases ha2 : 2 ∣ z.re
  · have ha4 : z.re ^ 2 ≡ 0 [ZMOD 4] := Int.sq_emod_four_of_even z.re ha2
    by_cases hb2 : 2 ∣ z.im
    · have hb4 : z.im ^ 2 ≡ 0 [ZMOD 4] := Int.sq_emod_four_of_even z.im hb2
      have hnorm4 : z.re ^ 2 - D * z.im ^ 2 ≡ 0 [ZMOD 4] := by
        simpa using ha4.sub ((Int.ModEq.refl D).mul hb4)
      have hnorm2 : (z.re ^ 2 - D * z.im ^ 2) % 2 = 0 := by
        have h := hnorm4.of_dvd (by norm_num : (2 : ℤ) ∣ 4)
        simpa using h.eq
      rw [RingOfIntegers.norm_zsqrtd] at hnodd
      omega
    · have hb4 : z.im ^ 2 ≡ 1 [ZMOD 4] := Int.sq_emod_four_of_odd z.im hb2
      have hd4mod : D ≡ 3 [ZMOD 4] := by exact hd4
      have hnorm4 : z.re ^ 2 - D * z.im ^ 2 ≡ 1 [ZMOD 4] := by
        calc
          z.re ^ 2 - D * z.im ^ 2 ≡ 0 - 3 * 1 [ZMOD 4] := ha4.sub (hd4mod.mul hb4)
          _ ≡ 1 [ZMOD 4] := by decide +revert
      exact hnorm4
  · have ha4 : z.re ^ 2 ≡ 1 [ZMOD 4] := Int.sq_emod_four_of_odd z.re ha2
    by_cases hb2 : 2 ∣ z.im
    · have hb4 : z.im ^ 2 ≡ 0 [ZMOD 4] := Int.sq_emod_four_of_even z.im hb2
      have hnorm4 : z.re ^ 2 - D * z.im ^ 2 ≡ 1 [ZMOD 4] := by
        simpa using ha4.sub ((Int.ModEq.refl D).mul hb4)
      exact hnorm4
    · have hb4 : z.im ^ 2 ≡ 1 [ZMOD 4] := Int.sq_emod_four_of_odd z.im hb2
      have hd4mod : D ≡ 3 [ZMOD 4] := by exact hd4
      have hnorm4 : z.re ^ 2 - D * z.im ^ 2 ≡ 2 [ZMOD 4] := by
        calc
          z.re ^ 2 - D * z.im ^ 2 ≡ 1 - 3 * 1 [ZMOD 4] := ha4.sub (hd4mod.mul hb4)
          _ ≡ 2 [ZMOD 4] := by decide +revert
      have hnorm2 : (z.re ^ 2 - D * z.im ^ 2) % 2 = 0 := by
        have h := hnorm4.of_dvd (by norm_num : (2 : ℤ) ∣ 4)
        simpa using h.eq
      rw [RingOfIntegers.norm_zsqrtd] at hnodd
      omega

private theorem zsqrtd_norm_emod_eight_eq_one_or_seven_of_param_mod_eight_two
    {D : ℤ} (z : Zsqrtd D) (hd8 : D % 8 = 2)
    (hnodd : (Zsqrtd.norm z) % 2 = 1) :
    Zsqrtd.norm z % 8 = 1 ∨ Zsqrtd.norm z % 8 = 7 := by
  rw [RingOfIntegers.norm_zsqrtd]
  have hd8mod : D ≡ 2 [ZMOD 8] := by exact hd8
  by_cases ha2 : 2 ∣ z.re
  · have ha4 : z.re ^ 2 ≡ 0 [ZMOD 4] := Int.sq_emod_four_of_even z.re ha2
    have hda2 : D ≡ 0 [ZMOD 2] := by
      have hd2 : D % 2 = 0 := by omega
      exact hd2
    have hnorm2 : (z.re ^ 2 - D * z.im ^ 2) % 2 = 0 := by
      have ha2mod : z.re ^ 2 ≡ 0 [ZMOD 2] :=
        ha4.of_dvd (by norm_num : (2 : ℤ) ∣ 4)
      have hprod2 : D * z.im ^ 2 ≡ 0 [ZMOD 2] := by
        simpa using hda2.mul (Int.ModEq.refl (z.im ^ 2))
      have hmod : z.re ^ 2 - D * z.im ^ 2 ≡ 0 [ZMOD 2] := by
        simpa using ha2mod.sub hprod2
      exact hmod.eq
    rw [RingOfIntegers.norm_zsqrtd] at hnodd
    omega
  · have ha8 : z.re ^ 2 ≡ 1 [ZMOD 8] := sq_emod_eight_of_odd z.re ha2
    by_cases hb2 : 2 ∣ z.im
    · have hb4 : z.im ^ 2 ≡ 0 [ZMOD 4] := Int.sq_emod_four_of_even z.im hb2
      have htwo_mul_b : (2 : ℤ) * z.im ^ 2 ≡ 0 [ZMOD 8] := by
        simpa using hb4.mul_left' (c := (2 : ℤ))
      have hdb : D * z.im ^ 2 ≡ 0 [ZMOD 8] :=
        (hd8mod.mul (Int.ModEq.refl (z.im ^ 2))).trans htwo_mul_b
      have hnorm8 : z.re ^ 2 - D * z.im ^ 2 ≡ 1 [ZMOD 8] := by
        simpa using ha8.sub hdb
      left
      exact hnorm8
    · have hb8 : z.im ^ 2 ≡ 1 [ZMOD 8] := sq_emod_eight_of_odd z.im hb2
      have hdb : D * z.im ^ 2 ≡ 2 [ZMOD 8] := by
        simpa using hd8mod.mul hb8
      have hnorm8 : z.re ^ 2 - D * z.im ^ 2 ≡ 7 [ZMOD 8] := by
        calc
          z.re ^ 2 - D * z.im ^ 2 ≡ 1 - 2 [ZMOD 8] := ha8.sub hdb
          _ ≡ 7 [ZMOD 8] := by decide +revert
      right
      exact hnorm8

private theorem zsqrtd_norm_emod_eight_eq_one_or_three_of_param_mod_eight_six
    {D : ℤ} (z : Zsqrtd D) (hd8 : D % 8 = 6)
    (hnodd : (Zsqrtd.norm z) % 2 = 1) :
    Zsqrtd.norm z % 8 = 1 ∨ Zsqrtd.norm z % 8 = 3 := by
  rw [RingOfIntegers.norm_zsqrtd]
  have hd8mod : D ≡ 6 [ZMOD 8] := by exact hd8
  by_cases ha2 : 2 ∣ z.re
  · have ha4 : z.re ^ 2 ≡ 0 [ZMOD 4] := Int.sq_emod_four_of_even z.re ha2
    have hda2 : D ≡ 0 [ZMOD 2] := by
      have hd2 : D % 2 = 0 := by omega
      exact hd2
    have hnorm2 : (z.re ^ 2 - D * z.im ^ 2) % 2 = 0 := by
      have ha2mod : z.re ^ 2 ≡ 0 [ZMOD 2] :=
        ha4.of_dvd (by norm_num : (2 : ℤ) ∣ 4)
      have hprod2 : D * z.im ^ 2 ≡ 0 [ZMOD 2] := by
        simpa using hda2.mul (Int.ModEq.refl (z.im ^ 2))
      have hmod : z.re ^ 2 - D * z.im ^ 2 ≡ 0 [ZMOD 2] := by
        simpa using ha2mod.sub hprod2
      exact hmod.eq
    rw [RingOfIntegers.norm_zsqrtd] at hnodd
    omega
  · have ha8 : z.re ^ 2 ≡ 1 [ZMOD 8] := sq_emod_eight_of_odd z.re ha2
    by_cases hb2 : 2 ∣ z.im
    · have hb4 : z.im ^ 2 ≡ 0 [ZMOD 4] := Int.sq_emod_four_of_even z.im hb2
      have hsix_mul_b : (6 : ℤ) * z.im ^ 2 ≡ 0 [ZMOD 8] := by
        have htwo_mul_b : (2 : ℤ) * z.im ^ 2 ≡ 0 [ZMOD 8] := by
          simpa using hb4.mul_left' (c := (2 : ℤ))
        have hfour_mul_b : (4 : ℤ) * z.im ^ 2 ≡ 0 [ZMOD 8] := by
          have h := hb4.mul_left' (c := (4 : ℤ))
          exact h.of_dvd (by norm_num : (8 : ℤ) ∣ 4 * 4)
        calc
          (6 : ℤ) * z.im ^ 2 = (2 : ℤ) * z.im ^ 2 + (4 : ℤ) * z.im ^ 2 := by ring
          _ ≡ 0 + 0 [ZMOD 8] := htwo_mul_b.add hfour_mul_b
          _ ≡ 0 [ZMOD 8] := by decide +revert
      have hdb : D * z.im ^ 2 ≡ 0 [ZMOD 8] :=
        (hd8mod.mul (Int.ModEq.refl (z.im ^ 2))).trans hsix_mul_b
      have hnorm8 : z.re ^ 2 - D * z.im ^ 2 ≡ 1 [ZMOD 8] := by
        simpa using ha8.sub hdb
      left
      exact hnorm8
    · have hb8 : z.im ^ 2 ≡ 1 [ZMOD 8] := sq_emod_eight_of_odd z.im hb2
      have hdb : D * z.im ^ 2 ≡ 6 [ZMOD 8] := by
        simpa using hd8mod.mul hb8
      have hnorm8 : z.re ^ 2 - D * z.im ^ 2 ≡ 3 [ZMOD 8] := by
        calc
          z.re ^ 2 - D * z.im ^ 2 ≡ 1 - 6 [ZMOD 8] := ha8.sub hdb
          _ ≡ 3 [ZMOD 8] := by decide +revert
      right
      exact hnorm8

/-- In the `ℤ[√d]` branch, nonnegative explicit norms prime to the `2`-primary
signed factor have trivial `2`-primary Kronecker value. -/
theorem kroneckerSymNat_twoPrimeDiscriminantFactor_zsqrtd_norm_eq_one
    {D : ℤ} [Fact (Squarefree D)]
    (z : Zsqrtd D) (hd4 : D % 4 ≠ 1) (hN_nonneg : 0 ≤ Zsqrtd.norm z)
    (hcop : Nat.Coprime (Zsqrtd.norm z).natAbs (twoPrimeDiscriminantFactor D).natAbs) :
    kroneckerSymNat (twoPrimeDiscriminantFactor D) (Zsqrtd.norm z).natAbs = 1 := by
  refine kroneckerSymNat_twoPrimeDiscriminantFactor_eq_one_of_mod_conditions ?_ ?_ ?_
  · intro hd2
    have hcop4 : Nat.Coprime (Zsqrtd.norm z).natAbs 4 := by
      simpa [twoPrimeDiscriminantFactor, hd2] using hcop
    have hnodd : (Zsqrtd.norm z) % 2 = 1 :=
      int_emod_two_eq_one_of_natAbs_coprime_of_two_dvd hN_nonneg hcop4
        (by norm_num : 2 ∣ 4)
    have hd43 : D % 4 = 3 := by omega
    have hmod := zsqrtd_norm_emod_four_eq_one_of_param_mod_four_three z hd43 hnodd
    have hcast : (((Zsqrtd.norm z).natAbs % 4 : ℕ) : ℤ) = 1 := by
      have habs := Int.natAbs_of_nonneg hN_nonneg
      omega
    omega
  · intro hd2 hd8
    have hcop8 : Nat.Coprime (Zsqrtd.norm z).natAbs 8 := by
      simpa [twoPrimeDiscriminantFactor, hd2, hd8] using hcop
    have hnodd : (Zsqrtd.norm z) % 2 = 1 :=
      int_emod_two_eq_one_of_natAbs_coprime_of_two_dvd hN_nonneg hcop8
        (by norm_num : 2 ∣ 8)
    rcases zsqrtd_norm_emod_eight_eq_one_or_seven_of_param_mod_eight_two z hd8 hnodd
      with hmod | hmod
    · left
      have hcast : (((Zsqrtd.norm z).natAbs % 8 : ℕ) : ℤ) = 1 := by
        have habs := Int.natAbs_of_nonneg hN_nonneg
        omega
      omega
    · right
      have hcast : (((Zsqrtd.norm z).natAbs % 8 : ℕ) : ℤ) = 7 := by
        have habs := Int.natAbs_of_nonneg hN_nonneg
        omega
      omega
  · intro hd2 hd8_ne
    have hcop8 : Nat.Coprime (Zsqrtd.norm z).natAbs 8 := by
      simpa [twoPrimeDiscriminantFactor, hd2, hd8_ne] using hcop
    have hnodd : (Zsqrtd.norm z) % 2 = 1 :=
      int_emod_two_eq_one_of_natAbs_coprime_of_two_dvd hN_nonneg hcop8
        (by norm_num : 2 ∣ 8)
    have hd4_ne_zero : D % 4 ≠ 0 := by
      intro hd40
      exact squarefree_int_not_dvd_four D (Fact.out : Squarefree D)
        (Int.dvd_of_emod_eq_zero hd40)
    have hd86 : D % 8 = 6 := by omega
    rcases zsqrtd_norm_emod_eight_eq_one_or_three_of_param_mod_eight_six z hd86 hnodd
      with hmod | hmod
    · left
      have hcast : (((Zsqrtd.norm z).natAbs % 8 : ℕ) : ℤ) = 1 := by
        have habs := Int.natAbs_of_nonneg hN_nonneg
        omega
      omega
    · right
      have hcast : (((Zsqrtd.norm z).natAbs % 8 : ℕ) : ℤ) = 3 := by
        have habs := Int.natAbs_of_nonneg hN_nonneg
        omega
      omega

private theorem legendreSym_zsqrtd_norm_eq_one_of_dvd_param
    {D : ℤ} {p : ℕ} [Fact p.Prime] (hpd : (p : ℤ) ∣ D) (z : Zsqrtd D)
    (hz : ¬ (p : ℤ) ∣ Zsqrtd.norm z) :
    legendreSym p (Zsqrtd.norm z) = 1 := by
  have hnorm_ne : ((Zsqrtd.norm z : ℤ) : ZMod p) ≠ 0 := by
    intro hzero
    exact hz ((ZMod.intCast_zmod_eq_zero_iff_dvd (Zsqrtd.norm z) p).mp hzero)
  refine (legendreSym.eq_one_iff p hnorm_ne).mpr ?_
  refine ⟨(z.re : ZMod p), ?_⟩
  have hD_zero : ((D : ℤ) : ZMod p) = 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd D p).mpr hpd
  rw [RingOfIntegers.norm_zsqrtd]
  push_cast
  rw [hD_zero]
  ring

private theorem legendreSym_zOnePlusSqrtOverTwo_norm_eq_one_of_dvd_discr
    {k : ℤ} {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    (hpd : (p : ℤ) ∣ 1 + 4 * k) (z : ZOnePlusSqrtdOverTwo k)
    (hz : ¬ (p : ℤ) ∣ QuadraticAlgebra.norm z) :
    legendreSym p (QuadraticAlgebra.norm z) = 1 := by
  have hnorm_ne : ((QuadraticAlgebra.norm z : ℤ) : ZMod p) ≠ 0 := by
    intro hzero
    exact hz ((ZMod.intCast_zmod_eq_zero_iff_dvd (QuadraticAlgebra.norm z) p).mp hzero)
  refine (legendreSym.eq_one_iff p hnorm_ne).mpr ?_
  let w : ZMod p := (2 : ZMod p) * (z.re : ZMod p) + (z.im : ZMod p)
  refine ⟨(2 : ZMod p)⁻¹ * w, ?_⟩
  have h2 : (2 : ZMod p) ≠ 0 :=
    Splitting.zmod_two_ne_zero_of_prime_ne_two p hp2
  have hD : (1 : ZMod p) + 4 * (k : ZMod p) = 0 := by
    have h := (ZMod.intCast_zmod_eq_zero_iff_dvd (1 + 4 * k) p).mpr hpd
    simpa using h
  have hk : (k : ZMod p) * 4 = -1 := by
    linear_combination hD
  rw [RingOfIntegers.norm_zOnePlusSqrtOverTwo]
  push_cast
  field_simp [w, h2]
  ring_nf
  rw [show (z.im : ZMod p) ^ 2 * (k : ZMod p) * 4 =
      ((k : ZMod p) * 4) * (z.im : ZMod p) ^ 2 by ring]
  rw [hk]
  ring

private theorem odd_ramified_dvd_param_of_mod_four_ne_one
    {D : ℤ} [Fact (Squarefree D)] [Fact (D ≠ 1)] {p : ℕ}
    (hp_ram : p ∈ ramifiedPrimes D) (hp2 : p ≠ 2) (hd4 : D % 4 ≠ 1) :
    (p : ℤ) ∣ D := by
  have hp_prime : p.Prime := prime_of_mem_ramifiedPrimes hp_ram
  have hp_dvd_disc : (p : ℤ) ∣ NumberField.discr (Qsqrtd (D : ℚ)) :=
    dvd_discr_of_mem_ramifiedPrimes hp_ram
  rw [RingOfIntegers.discr_formula,
    RingOfIntegers.discrFormula_of_mod_four_ne_one hd4] at hp_dvd_disc
  have hp_int_prime : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp_prime
  rcases hp_int_prime.dvd_or_dvd hp_dvd_disc with hp4 | hpD
  · have hp_dvd_four_nat : p ∣ 4 := by
      exact_mod_cast hp4
    have hp_le4 : p ≤ 4 := Nat.le_of_dvd (by norm_num) hp_dvd_four_nat
    interval_cases p
    · norm_num at hp_prime
    · norm_num at hp_prime
    · exact (hp2 rfl).elim
    · norm_num at hp_dvd_four_nat
    · norm_num at hp_prime
  · exact hpD

private theorem odd_ramified_dvd_param_of_mod_four_eq_one
    {D : ℤ} [Fact (Squarefree D)] [Fact (D ≠ 1)] {p : ℕ}
    (hp_ram : p ∈ ramifiedPrimes D) (hd4 : D % 4 = 1) :
    (p : ℤ) ∣ D := by
  have hp_dvd_disc : (p : ℤ) ∣ NumberField.discr (Qsqrtd (D : ℚ)) :=
    dvd_discr_of_mem_ramifiedPrimes hp_ram
  simpa [RingOfIntegers.discr_formula, RingOfIntegers.discrFormula_of_mod_four_eq_one hd4]
    using hp_dvd_disc

private theorem two_not_mem_ramifiedPrimes_of_mod_four_eq_one
    {D : ℤ} [Fact (Squarefree D)] [Fact (D ≠ 1)] (hd4 : D % 4 = 1) :
    2 ∉ ramifiedPrimes D := by
  intro h2ram
  have h2_dvd_disc : (2 : ℤ) ∣ NumberField.discr (Qsqrtd (D : ℚ)) :=
    dvd_discr_of_mem_ramifiedPrimes h2ram
  have h2D : (2 : ℤ) ∣ D := by
    simpa [RingOfIntegers.discr_formula, RingOfIntegers.discrFormula_of_mod_four_eq_one hd4]
      using h2_dvd_disc
  have hd2 : D % 2 = 0 := Int.emod_eq_zero_of_dvd h2D
  omega

/-- In the `ℤ[√d]` branch, nonnegative explicit norms prime to any signed
prime-discriminant factor have trivial Kronecker value. -/
theorem kroneckerSymNat_signedFactor_zsqrtd_norm_eq_one
    {D : ℤ} [Fact (Squarefree D)] [Fact (D ≠ 1)]
    (q : {q // q ∈ signedPrimeDiscriminantFactors D})
    (z : Zsqrtd D) (hd4 : D % 4 ≠ 1) (hN_nonneg : 0 ≤ Zsqrtd.norm z)
    (hcop : Nat.Coprime (Zsqrtd.norm z).natAbs q.1.natAbs) :
    kroneckerSymNat q.1 (Zsqrtd.norm z).natAbs = 1 := by
  rcases eq_twoPrimeDiscriminantFactor_or_exists_oddPrimeDiscriminantFactor_of_mem
      (d := D) q.property with htwo | hodd
  · rcases htwo with ⟨hq, _h2ram⟩
    rw [hq] at hcop ⊢
    exact kroneckerSymNat_twoPrimeDiscriminantFactor_zsqrtd_norm_eq_one
      z hd4 hN_nonneg hcop
  · rcases hodd with ⟨p, hp_ram, hp_prime, hp2, hq⟩
    rw [hq] at hcop ⊢
    letI : Fact p.Prime := ⟨hp_prime⟩
    rw [kroneckerSymNat_oddPrimeDiscriminantFactor_eq_legendreSym hp2]
    have hcop_p : Nat.Coprime (Zsqrtd.norm z).natAbs p := by
      simpa [natAbs_oddPrimeDiscriminantFactor] using hcop
    have hnot_p_nat : ¬ p ∣ (Zsqrtd.norm z).natAbs :=
      (hp_prime.coprime_iff_not_dvd).mp hcop_p.symm
    have hnot_p_int : ¬ (p : ℤ) ∣ Zsqrtd.norm z := by
      intro hdiv
      exact hnot_p_nat (Int.natCast_dvd.mp hdiv)
    have hpd : (p : ℤ) ∣ D :=
      odd_ramified_dvd_param_of_mod_four_ne_one hp_ram hp2 hd4
    have h_absnorm_int : (((Zsqrtd.norm z).natAbs : ℕ) : ℤ) = Zsqrtd.norm z :=
      Int.natAbs_of_nonneg hN_nonneg
    rw [h_absnorm_int]
    exact legendreSym_zsqrtd_norm_eq_one_of_dvd_param hpd z hnot_p_int

/-- In the half-integral branch, nonnegative explicit norms prime to any signed
prime-discriminant factor have trivial Kronecker value. -/
theorem kroneckerSymNat_signedFactor_zOnePlusSqrtOverTwo_norm_eq_one
    {D k : ℤ} [Fact (Squarefree D)] [Fact (D ≠ 1)]
    (q : {q // q ∈ signedPrimeDiscriminantFactors D})
    (z : ZOnePlusSqrtdOverTwo k) (hk : D = 1 + 4 * k)
    (hN_nonneg : 0 ≤ QuadraticAlgebra.norm z)
    (hcop : Nat.Coprime (QuadraticAlgebra.norm z).natAbs q.1.natAbs) :
    kroneckerSymNat q.1 (QuadraticAlgebra.norm z).natAbs = 1 := by
  have hd4 : D % 4 = 1 := by
    rw [hk]
    omega
  rcases eq_twoPrimeDiscriminantFactor_or_exists_oddPrimeDiscriminantFactor_of_mem
      (d := D) q.property with htwo | hodd
  · rcases htwo with ⟨_hq, h2ram⟩
    exact (two_not_mem_ramifiedPrimes_of_mod_four_eq_one hd4 h2ram).elim
  · rcases hodd with ⟨p, hp_ram, hp_prime, hp2, hq⟩
    rw [hq] at hcop ⊢
    letI : Fact p.Prime := ⟨hp_prime⟩
    rw [kroneckerSymNat_oddPrimeDiscriminantFactor_eq_legendreSym hp2]
    have hcop_p : Nat.Coprime (QuadraticAlgebra.norm z).natAbs p := by
      simpa [natAbs_oddPrimeDiscriminantFactor] using hcop
    have hnot_p_nat : ¬ p ∣ (QuadraticAlgebra.norm z).natAbs :=
      (hp_prime.coprime_iff_not_dvd).mp hcop_p.symm
    have hnot_p_int : ¬ (p : ℤ) ∣ QuadraticAlgebra.norm z := by
      intro hdiv
      exact hnot_p_nat (Int.natCast_dvd.mp hdiv)
    have hpd : (p : ℤ) ∣ D :=
      odd_ramified_dvd_param_of_mod_four_eq_one hp_ram hd4
    have h_absnorm_int :
        (((QuadraticAlgebra.norm z).natAbs : ℕ) : ℤ) = QuadraticAlgebra.norm z :=
      Int.natAbs_of_nonneg hN_nonneg
    rw [h_absnorm_int]
    exact legendreSym_zOnePlusSqrtOverTwo_norm_eq_one_of_dvd_discr hp2
      (by simpa [hk] using hpd) z hnot_p_int

/-- In the `d % 4 ≠ 1` ring-of-integers branch, a principal ideal generated by
an element with nonnegative algebra norm has trivial Kronecker value at every
signed prime-discriminant factor coprime to its absolute norm. -/
theorem kroneckerSymNat_signedFactor_absNorm_span_eq_one_of_mod_four_ne_one
    {D : ℤ} [Fact (Squarefree D)] [Fact (D ≠ 1)]
    (q : {q // q ∈ signedPrimeDiscriminantFactors D})
    {α : NumberField.RingOfIntegers (Qsqrtd (D : ℚ))} (hd4 : D % 4 ≠ 1)
    (hN_nonneg : 0 ≤ Algebra.norm ℤ α)
    (hcop : Nat.Coprime
      (Ideal.absNorm (Ideal.span
        ({α} : Set (NumberField.RingOfIntegers (Qsqrtd (D : ℚ)))))) q.1.natAbs) :
    kroneckerSymNat q.1
      (Ideal.absNorm (Ideal.span
        ({α} : Set (NumberField.RingOfIntegers (Qsqrtd (D : ℚ)))))) = 1 := by
  let z : Zsqrtd D :=
    (RingOfIntegers.ringOfIntegers_equiv_zsqrtd_of_mod_four_ne_one D hd4) α
  have hnorm : Algebra.norm ℤ α = Zsqrtd.norm z := by
    simpa [z] using RingOfIntegers.algebraNorm_eq_zsqrtd_norm_of_mod_four_ne_one
      (d := D) hd4 α
  have hz_nonneg : 0 ≤ Zsqrtd.norm z := by
    rwa [hnorm] at hN_nonneg
  have hcop_z : Nat.Coprime (Zsqrtd.norm z).natAbs q.1.natAbs := by
    simpa [Ideal.absNorm_span_singleton, hnorm] using hcop
  rw [Ideal.absNorm_span_singleton, hnorm]
  exact kroneckerSymNat_signedFactor_zsqrtd_norm_eq_one q z hd4 hz_nonneg hcop_z

/-- In the `d % 4 = 1` ring-of-integers branch, a principal ideal generated by
an element with nonnegative algebra norm has trivial Kronecker value at every
signed prime-discriminant factor coprime to its absolute norm. -/
theorem kroneckerSymNat_signedFactor_absNorm_span_eq_one_of_mod_four_eq_one
    {D : ℤ} [Fact (Squarefree D)] [Fact (D ≠ 1)]
    (q : {q // q ∈ signedPrimeDiscriminantFactors D})
    {α : NumberField.RingOfIntegers (Qsqrtd (D : ℚ))} (hd4 : D % 4 = 1)
    (hN_nonneg : 0 ≤ Algebra.norm ℤ α)
    (hcop : Nat.Coprime
      (Ideal.absNorm (Ideal.span
        ({α} : Set (NumberField.RingOfIntegers (Qsqrtd (D : ℚ)))))) q.1.natAbs) :
    kroneckerSymNat q.1
      (Ideal.absNorm (Ideal.span
        ({α} : Set (NumberField.RingOfIntegers (Qsqrtd (D : ℚ)))))) = 1 := by
  obtain ⟨k, hk⟩ := RingOfIntegers.exists_k_of_mod_four_eq_one hd4
  let z : ZOnePlusSqrtdOverTwo k :=
    (RingOfIntegers.ringOfIntegers_equiv_zOnePlusSqrtOverTwo_of_eq D k hk) α
  have hnorm : Algebra.norm ℤ α = QuadraticAlgebra.norm z := by
    simpa [z] using RingOfIntegers.algebraNorm_eq_zOnePlusSqrtOverTwo_norm_of_eq
      (d := D) k hk α
  have hz_nonneg : 0 ≤ QuadraticAlgebra.norm z := by
    rwa [hnorm] at hN_nonneg
  have hcop_z : Nat.Coprime (QuadraticAlgebra.norm z).natAbs q.1.natAbs := by
    simpa [Ideal.absNorm_span_singleton, hnorm] using hcop
  rw [Ideal.absNorm_span_singleton, hnorm]
  exact kroneckerSymNat_signedFactor_zOnePlusSqrtOverTwo_norm_eq_one q z hk hz_nonneg
    hcop_z

/-- A principal ideal generated by an element with nonnegative algebra norm has
trivial Kronecker value at every signed prime-discriminant factor coprime to its
absolute norm. -/
theorem kroneckerSymNat_signedFactor_absNorm_span_eq_one_of_algebraNorm_nonneg
    {D : ℤ} [Fact (Squarefree D)] [Fact (D ≠ 1)]
    (q : {q // q ∈ signedPrimeDiscriminantFactors D})
    {α : NumberField.RingOfIntegers (Qsqrtd (D : ℚ))}
    (hN_nonneg : 0 ≤ Algebra.norm ℤ α)
    (hcop : Nat.Coprime
      (Ideal.absNorm (Ideal.span
        ({α} : Set (NumberField.RingOfIntegers (Qsqrtd (D : ℚ)))))) q.1.natAbs) :
    kroneckerSymNat q.1
      (Ideal.absNorm (Ideal.span
        ({α} : Set (NumberField.RingOfIntegers (Qsqrtd (D : ℚ)))))) = 1 := by
  by_cases hd4 : D % 4 = 1
  · exact kroneckerSymNat_signedFactor_absNorm_span_eq_one_of_mod_four_eq_one
      q hd4 hN_nonneg hcop
  · exact kroneckerSymNat_signedFactor_absNorm_span_eq_one_of_mod_four_ne_one
      q hd4 hN_nonneg hcop

/-- The raw signed-factor character is trivial on a principal ideal generated by an
element of nonnegative algebra norm whose principal absolute norm is coprime to the
signed factor. -/
theorem genusCharacterOfSignedFactorRaw_span_eq_one_of_algebraNorm_nonneg
    {D : ℤ} [Fact (Squarefree D)] [Fact (D ≠ 1)]
    (q : {q // q ∈ signedPrimeDiscriminantFactors D})
    {α : NumberField.RingOfIntegers (Qsqrtd (D : ℚ))}
    (hN_nonneg : 0 ≤ Algebra.norm ℤ α)
    (hcop : Nat.Coprime
      (Ideal.absNorm (Ideal.span
        ({α} : Set (NumberField.RingOfIntegers (Qsqrtd (D : ℚ)))))) q.1.natAbs) :
    genusCharacterOfSignedFactorRaw D q
        ⟨Ideal.span ({α} : Set (NumberField.RingOfIntegers (Qsqrtd (D : ℚ)))), hcop⟩ =
      1 := by
  ext
  simpa [genusCharacterOfSignedFactorRaw_val] using
    kroneckerSymNat_signedFactor_absNorm_span_eq_one_of_algebraNorm_nonneg
      q hN_nonneg hcop

/-- A totally positive algebraic integer in `𝓞(Q(√D))` has nonnegative
integer algebra norm. In the imaginary case this is the existing quadratic norm
positivity; in the real case it follows by evaluating at the two explicit real
embeddings. -/
theorem algebraNorm_nonneg_of_isTotallyPositive
    {D : ℤ} [Fact (Squarefree D)] [Fact (D ≠ 1)]
    {α : NumberField.RingOfIntegers (Qsqrtd (D : ℚ))}
    (hpos : NarrowClassGroup.IsTotallyPositive
      (algebraMap (NumberField.RingOfIntegers (Qsqrtd (D : ℚ)))
        (FractionRing (NumberField.RingOfIntegers (Qsqrtd (D : ℚ)))) α)) :
    0 ≤ Algebra.norm ℤ α := by
  by_cases hDneg : D < 0
  · exact RingOfIntegers.algebraNorm_nonneg_of_neg D hDneg α
  have hD_ne_zero : D ≠ 0 :=
    Squarefree.ne_zero (Fact.out : Squarefree D)
  have hDpos : 0 < D := by omega
  have hD_nonneg_real : 0 ≤ (D : ℝ) := by exact_mod_cast le_of_lt hDpos
  let e : FractionRing (NumberField.RingOfIntegers (Qsqrtd (D : ℚ))) ≃ₐ[
      NumberField.RingOfIntegers (Qsqrtd (D : ℚ))] Qsqrtd (D : ℚ) :=
    FractionRing.algEquiv
      (A := NumberField.RingOfIntegers (Qsqrtd (D : ℚ))) (Qsqrtd (D : ℚ))
  let σpos : FractionRing (NumberField.RingOfIntegers (Qsqrtd (D : ℚ))) →+* ℝ :=
    (Qsqrtd.realEmbeddingPos D hD_nonneg_real).toRingHom.comp e.toRingHom
  let σneg : FractionRing (NumberField.RingOfIntegers (Qsqrtd (D : ℚ))) →+* ℝ :=
    (Qsqrtd.realEmbeddingNeg D hD_nonneg_real).toRingHom.comp e.toRingHom
  have hpos_pos : 0 < Qsqrtd.realEmbeddingPos D hD_nonneg_real
      (α : Qsqrtd (D : ℚ)) := by
    simpa [σpos, e] using hpos σpos
  have hpos_neg : 0 < Qsqrtd.realEmbeddingNeg D hD_nonneg_real
      (α : Qsqrtd (D : ℚ)) := by
    simpa [σneg, e] using hpos σneg
  have hnorm_pos_real : 0 < (Qsqrtd.norm (α : Qsqrtd (D : ℚ)) : ℝ) :=
    Qsqrtd.norm_pos_of_realEmbedding_pos D hD_nonneg_real hpos_pos hpos_neg
  have hnorm_pos_rat : 0 < Qsqrtd.norm (α : Qsqrtd (D : ℚ)) := by
    exact_mod_cast hnorm_pos_real
  have hcast : (0 : ℚ) ≤ (Algebra.norm ℤ α : ℚ) := by
    rw [Algebra.coe_norm_int (K := Qsqrtd (D : ℚ)),
      Qsqrtd.algebraNorm_ratAlgebra_eq_qsqrtdNorm]
    exact le_of_lt hnorm_pos_rat
  exact_mod_cast hcast

/-- If a totally positive fraction-field unit is represented as `a / b`, then
the integral element `a * b` has nonnegative algebra norm. Multiplying by the
positive square `b²` clears the denominator without changing signs at real
embeddings. -/
theorem algebraNorm_nonneg_mul_of_isTotallyPositive_mk'
    {D : ℤ} [Fact (Squarefree D)] [Fact (D ≠ 1)]
    {x : (FractionRing (NumberField.RingOfIntegers (Qsqrtd (D : ℚ))))ˣ}
    {a b : NumberField.RingOfIntegers (Qsqrtd (D : ℚ))}
    (hb : b ≠ 0)
    (hmk : IsLocalization.mk'
        (FractionRing (NumberField.RingOfIntegers (Qsqrtd (D : ℚ)))) a
        ⟨b, mem_nonZeroDivisors_iff_ne_zero.mpr hb⟩ =
      (x : FractionRing (NumberField.RingOfIntegers (Qsqrtd (D : ℚ)))))
    (hxpos : NarrowClassGroup.IsTotallyPositive
      (x : FractionRing (NumberField.RingOfIntegers (Qsqrtd (D : ℚ))))) :
    0 ≤ Algebra.norm ℤ (a * b) := by
  refine algebraNorm_nonneg_of_isTotallyPositive ?_
  intro σ
  have hb_map_ne :
      algebraMap (NumberField.RingOfIntegers (Qsqrtd (D : ℚ)))
          (FractionRing (NumberField.RingOfIntegers (Qsqrtd (D : ℚ)))) b ≠ 0 :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors
      (mem_nonZeroDivisors_iff_ne_zero.mpr hb)
  have hmul :
      algebraMap (NumberField.RingOfIntegers (Qsqrtd (D : ℚ)))
          (FractionRing (NumberField.RingOfIntegers (Qsqrtd (D : ℚ)))) (a * b) =
        (x : FractionRing (NumberField.RingOfIntegers (Qsqrtd (D : ℚ)))) *
          algebraMap (NumberField.RingOfIntegers (Qsqrtd (D : ℚ)))
            (FractionRing (NumberField.RingOfIntegers (Qsqrtd (D : ℚ)))) b ^ 2 := by
    rw [map_mul]
    rw [← hmk, IsFractionRing.mk'_eq_div]
    field_simp [hb_map_ne]
  rw [hmul, map_mul, map_pow]
  exact mul_pos (hxpos σ)
    (sq_pos_of_ne_zero ((_root_.map_ne_zero σ).mpr hb_map_ne))

/-- A denominator-cleared principal relation is enough to compare raw
signed-factor characters: a nonnegative-norm principal multiplier is invisible,
and a square principal multiplier is invisible. -/
theorem genusCharacterOfSignedFactorRaw_eq_of_span_mul_eq_span_sq_mul
    {D : ℤ} [Fact (Squarefree D)] [Fact (D ≠ 1)]
    (q : {q // q ∈ signedPrimeDiscriminantFactors D})
    (I J : signedFactorCoprimeIdealSubmonoid D q)
    {α β : NumberField.RingOfIntegers (Qsqrtd (D : ℚ))}
    (hα_nonneg : 0 ≤ Algebra.norm ℤ α)
    (hαcop : Nat.Coprime
      (Ideal.absNorm (Ideal.span
        ({α} : Set (NumberField.RingOfIntegers (Qsqrtd (D : ℚ)))))) q.1.natAbs)
    (hβcop : Nat.Coprime
      (Ideal.absNorm (Ideal.span
        ({β} : Set (NumberField.RingOfIntegers (Qsqrtd (D : ℚ)))))) q.1.natAbs)
    (hprod : Ideal.span
        ({α} : Set (NumberField.RingOfIntegers (Qsqrtd (D : ℚ)))) *
          (I : Ideal (NumberField.RingOfIntegers (Qsqrtd (D : ℚ)))) =
        Ideal.span
          ({β} : Set (NumberField.RingOfIntegers (Qsqrtd (D : ℚ)))) *
          Ideal.span
            ({β} : Set (NumberField.RingOfIntegers (Qsqrtd (D : ℚ)))) *
          (J : Ideal (NumberField.RingOfIntegers (Qsqrtd (D : ℚ))))) :
    genusCharacterOfSignedFactorRaw D q I =
      genusCharacterOfSignedFactorRaw D q J := by
  let A : signedFactorCoprimeIdealSubmonoid D q :=
    ⟨Ideal.span ({α} : Set (NumberField.RingOfIntegers (Qsqrtd (D : ℚ)))), hαcop⟩
  let B : signedFactorCoprimeIdealSubmonoid D q :=
    ⟨Ideal.span ({β} : Set (NumberField.RingOfIntegers (Qsqrtd (D : ℚ)))), hβcop⟩
  have hprod' : I * A = J * B ^ 2 := by
    apply Subtype.ext
    change (I : Ideal (NumberField.RingOfIntegers (Qsqrtd (D : ℚ)))) *
        (A : Ideal (NumberField.RingOfIntegers (Qsqrtd (D : ℚ)))) =
      (J : Ideal (NumberField.RingOfIntegers (Qsqrtd (D : ℚ)))) *
        ((B : Ideal (NumberField.RingOfIntegers (Qsqrtd (D : ℚ)))) ^ 2)
    dsimp [A, B]
    rw [pow_two]
    change (I : Ideal (NumberField.RingOfIntegers (Qsqrtd (D : ℚ)))) *
        Ideal.span ({α} : Set (NumberField.RingOfIntegers (Qsqrtd (D : ℚ)))) =
      (J : Ideal (NumberField.RingOfIntegers (Qsqrtd (D : ℚ)))) *
        (Ideal.span ({β} : Set (NumberField.RingOfIntegers (Qsqrtd (D : ℚ)))) *
          Ideal.span ({β} : Set (NumberField.RingOfIntegers (Qsqrtd (D : ℚ)))))
    calc
      (I : Ideal (NumberField.RingOfIntegers (Qsqrtd (D : ℚ)))) *
          Ideal.span ({α} : Set (NumberField.RingOfIntegers (Qsqrtd (D : ℚ)))) =
        Ideal.span ({α} : Set (NumberField.RingOfIntegers (Qsqrtd (D : ℚ)))) *
          (I : Ideal (NumberField.RingOfIntegers (Qsqrtd (D : ℚ)))) := by
          rw [mul_comm]
      _ =
        Ideal.span ({β} : Set (NumberField.RingOfIntegers (Qsqrtd (D : ℚ)))) *
          Ideal.span ({β} : Set (NumberField.RingOfIntegers (Qsqrtd (D : ℚ)))) *
          (J : Ideal (NumberField.RingOfIntegers (Qsqrtd (D : ℚ)))) := hprod
      _ = (J : Ideal (NumberField.RingOfIntegers (Qsqrtd (D : ℚ)))) *
        (Ideal.span ({β} : Set (NumberField.RingOfIntegers (Qsqrtd (D : ℚ)))) *
          Ideal.span ({β} : Set (NumberField.RingOfIntegers (Qsqrtd (D : ℚ))))) := by
          ac_rfl
  have hA :
      genusCharacterOfSignedFactorRaw D q A = 1 :=
    genusCharacterOfSignedFactorRaw_span_eq_one_of_algebraNorm_nonneg q hα_nonneg hαcop
  have hB :
      genusCharacterOfSignedFactorRaw D q (B ^ 2) = 1 :=
    genusCharacterOfSignedFactorRaw_sq D q B
  exact genusCharacterOfSignedFactorRaw_eq_of_mul_eq_of_raw_eq D q I J A (B ^ 2)
    hprod' (by rw [hA, hB])

/-- A denominator-cleared principal relation coming from a totally positive
fraction-field multiplier compares raw signed-factor characters, once the
resulting principal ideals are known to remain coprime to the signed factor. -/
theorem genusCharacterOfSignedFactorRaw_eq_of_span_mul_eq_span_mul_of_isTotallyPositive_mk'
    {D : ℤ} [Fact (Squarefree D)] [Fact (D ≠ 1)]
    (q : {q // q ∈ signedPrimeDiscriminantFactors D})
    (I J : signedFactorCoprimeIdealSubmonoid D q)
    {x : (FractionRing (NumberField.RingOfIntegers (Qsqrtd (D : ℚ))))ˣ}
    {a b : NumberField.RingOfIntegers (Qsqrtd (D : ℚ))}
    (hb : b ≠ 0)
    (hmk : IsLocalization.mk'
        (FractionRing (NumberField.RingOfIntegers (Qsqrtd (D : ℚ)))) a
        ⟨b, mem_nonZeroDivisors_iff_ne_zero.mpr hb⟩ =
      (x : FractionRing (NumberField.RingOfIntegers (Qsqrtd (D : ℚ)))))
    (hxpos : NarrowClassGroup.IsTotallyPositive
      (x : FractionRing (NumberField.RingOfIntegers (Qsqrtd (D : ℚ)))))
    (habcop : Nat.Coprime
      (Ideal.absNorm (Ideal.span
        ({a * b} : Set (NumberField.RingOfIntegers (Qsqrtd (D : ℚ)))))) q.1.natAbs)
    (hbcop : Nat.Coprime
      (Ideal.absNorm (Ideal.span
        ({b} : Set (NumberField.RingOfIntegers (Qsqrtd (D : ℚ)))))) q.1.natAbs)
    (hprod : Ideal.span
        ({a} : Set (NumberField.RingOfIntegers (Qsqrtd (D : ℚ)))) *
          (I : Ideal (NumberField.RingOfIntegers (Qsqrtd (D : ℚ)))) =
        Ideal.span ({b} : Set (NumberField.RingOfIntegers (Qsqrtd (D : ℚ)))) *
          (J : Ideal (NumberField.RingOfIntegers (Qsqrtd (D : ℚ))))) :
    genusCharacterOfSignedFactorRaw D q I =
      genusCharacterOfSignedFactorRaw D q J := by
  have hab_nonneg : 0 ≤ Algebra.norm ℤ (a * b) :=
    algebraNorm_nonneg_mul_of_isTotallyPositive_mk' hb hmk hxpos
  refine genusCharacterOfSignedFactorRaw_eq_of_span_mul_eq_span_sq_mul
    q I J hab_nonneg habcop hbcop ?_
  calc
    Ideal.span ({a * b} : Set (NumberField.RingOfIntegers (Qsqrtd (D : ℚ)))) *
        (I : Ideal (NumberField.RingOfIntegers (Qsqrtd (D : ℚ)))) =
      (Ideal.span ({a} : Set (NumberField.RingOfIntegers (Qsqrtd (D : ℚ)))) *
          Ideal.span ({b} : Set (NumberField.RingOfIntegers (Qsqrtd (D : ℚ))))) *
        (I : Ideal (NumberField.RingOfIntegers (Qsqrtd (D : ℚ)))) := by
        rw [Ideal.span_singleton_mul_span_singleton]
    _ =
      Ideal.span ({b} : Set (NumberField.RingOfIntegers (Qsqrtd (D : ℚ)))) *
        (Ideal.span ({a} : Set (NumberField.RingOfIntegers (Qsqrtd (D : ℚ)))) *
          (I : Ideal (NumberField.RingOfIntegers (Qsqrtd (D : ℚ))))) := by
        ac_rfl
    _ =
      Ideal.span ({b} : Set (NumberField.RingOfIntegers (Qsqrtd (D : ℚ)))) *
        (Ideal.span ({b} : Set (NumberField.RingOfIntegers (Qsqrtd (D : ℚ)))) *
          (J : Ideal (NumberField.RingOfIntegers (Qsqrtd (D : ℚ))))) := by
        rw [hprod]
    _ =
      Ideal.span ({b} : Set (NumberField.RingOfIntegers (Qsqrtd (D : ℚ)))) *
        Ideal.span ({b} : Set (NumberField.RingOfIntegers (Qsqrtd (D : ℚ)))) *
          (J : Ideal (NumberField.RingOfIntegers (Qsqrtd (D : ℚ)))) := by
        ac_rfl

/-- In a relation `(a) I = (b) J` between signed-factor-coprime ideals, if
`(b)` is coprime to the signed factor then `(a)` is coprime to it as well. -/
theorem absNorm_span_left_coprime_of_span_mul_eq_span_mul
    {D : ℤ} [Fact (Squarefree D)] [Fact (D ≠ 1)]
    (q : {q // q ∈ signedPrimeDiscriminantFactors D})
    (I J : signedFactorCoprimeIdealSubmonoid D q)
    {a b : NumberField.RingOfIntegers (Qsqrtd (D : ℚ))}
    (hbcop : Nat.Coprime
      (Ideal.absNorm (Ideal.span
        ({b} : Set (NumberField.RingOfIntegers (Qsqrtd (D : ℚ)))))) q.1.natAbs)
    (hprod : Ideal.span
        ({a} : Set (NumberField.RingOfIntegers (Qsqrtd (D : ℚ)))) *
          (I : Ideal (NumberField.RingOfIntegers (Qsqrtd (D : ℚ)))) =
        Ideal.span ({b} : Set (NumberField.RingOfIntegers (Qsqrtd (D : ℚ)))) *
          (J : Ideal (NumberField.RingOfIntegers (Qsqrtd (D : ℚ))))) :
    Nat.Coprime
      (Ideal.absNorm (Ideal.span
        ({a} : Set (NumberField.RingOfIntegers (Qsqrtd (D : ℚ)))))) q.1.natAbs := by
  have hnorm := congrArg Ideal.absNorm hprod
  rw [Ideal.absNorm.map_mul, Ideal.absNorm.map_mul] at hnorm
  have hright : Nat.Coprime
      (Ideal.absNorm (Ideal.span
          ({b} : Set (NumberField.RingOfIntegers (Qsqrtd (D : ℚ))))) *
        Ideal.absNorm (J : Ideal (NumberField.RingOfIntegers (Qsqrtd (D : ℚ)))))
      q.1.natAbs :=
    Nat.Coprime.mul_left hbcop J.property
  have hleft : Nat.Coprime
      (Ideal.absNorm (Ideal.span
          ({a} : Set (NumberField.RingOfIntegers (Qsqrtd (D : ℚ))))) *
        Ideal.absNorm (I : Ideal (NumberField.RingOfIntegers (Qsqrtd (D : ℚ)))))
      q.1.natAbs := by
    rw [hnorm]
    exact hright
  exact Nat.Coprime.coprime_dvd_left (Nat.dvd_mul_right _ _) hleft

/-- In a relation `(a) I = (b) J` between signed-factor-coprime ideals, if
`(b)` is coprime to the signed factor then so is the principal ideal `(ab)`. -/
theorem absNorm_span_mul_coprime_of_span_mul_eq_span_mul
    {D : ℤ} [Fact (Squarefree D)] [Fact (D ≠ 1)]
    (q : {q // q ∈ signedPrimeDiscriminantFactors D})
    (I J : signedFactorCoprimeIdealSubmonoid D q)
    {a b : NumberField.RingOfIntegers (Qsqrtd (D : ℚ))}
    (hbcop : Nat.Coprime
      (Ideal.absNorm (Ideal.span
        ({b} : Set (NumberField.RingOfIntegers (Qsqrtd (D : ℚ)))))) q.1.natAbs)
    (hprod : Ideal.span
        ({a} : Set (NumberField.RingOfIntegers (Qsqrtd (D : ℚ)))) *
          (I : Ideal (NumberField.RingOfIntegers (Qsqrtd (D : ℚ)))) =
        Ideal.span ({b} : Set (NumberField.RingOfIntegers (Qsqrtd (D : ℚ)))) *
          (J : Ideal (NumberField.RingOfIntegers (Qsqrtd (D : ℚ))))) :
    Nat.Coprime
      (Ideal.absNorm (Ideal.span
        ({a * b} : Set (NumberField.RingOfIntegers (Qsqrtd (D : ℚ)))))) q.1.natAbs := by
  have hacop :=
    absNorm_span_left_coprime_of_span_mul_eq_span_mul q I J hbcop hprod
  rw [← Ideal.span_singleton_mul_span_singleton, Ideal.absNorm.map_mul]
  exact Nat.Coprime.mul_left hacop hbcop

/-- A denominator-cleared integral representative with denominator coprime to
the signed factor is enough to compare the raw signed-factor characters. The
coprimality of the cleared numerator follows from the ideal relation. -/
theorem genusCharacterOfSignedFactorRaw_eq_of_exists_denominator_coprime_mk'
    {D : ℤ} [Fact (Squarefree D)] [Fact (D ≠ 1)]
    (q : {q // q ∈ signedPrimeDiscriminantFactors D})
    (I J : signedFactorCoprimeIdealSubmonoid D q)
    {x : (FractionRing (NumberField.RingOfIntegers (Qsqrtd (D : ℚ))))ˣ}
    (hxpos : NarrowClassGroup.IsTotallyPositive
      (x : FractionRing (NumberField.RingOfIntegers (Qsqrtd (D : ℚ)))))
    (hrep : ∃ a b : NumberField.RingOfIntegers (Qsqrtd (D : ℚ)), ∃ hb : b ≠ 0,
      IsLocalization.mk'
          (FractionRing (NumberField.RingOfIntegers (Qsqrtd (D : ℚ)))) a
          ⟨b, mem_nonZeroDivisors_iff_ne_zero.mpr hb⟩ =
        (x : FractionRing (NumberField.RingOfIntegers (Qsqrtd (D : ℚ)))) ∧
      Nat.Coprime
        (Ideal.absNorm (Ideal.span
          ({b} : Set (NumberField.RingOfIntegers (Qsqrtd (D : ℚ)))))) q.1.natAbs ∧
      Ideal.span ({a} : Set (NumberField.RingOfIntegers (Qsqrtd (D : ℚ)))) *
          (I : Ideal (NumberField.RingOfIntegers (Qsqrtd (D : ℚ)))) =
        Ideal.span ({b} : Set (NumberField.RingOfIntegers (Qsqrtd (D : ℚ)))) *
          (J : Ideal (NumberField.RingOfIntegers (Qsqrtd (D : ℚ))))) :
    genusCharacterOfSignedFactorRaw D q I =
      genusCharacterOfSignedFactorRaw D q J := by
  rcases hrep with ⟨a, b, hb, hmk, hbcop, hprod⟩
  have habcop :
      Nat.Coprime
        (Ideal.absNorm (Ideal.span
          ({a * b} : Set (NumberField.RingOfIntegers (Qsqrtd (D : ℚ)))))) q.1.natAbs :=
    absNorm_span_mul_coprime_of_span_mul_eq_span_mul q I J hbcop hprod
  exact genusCharacterOfSignedFactorRaw_eq_of_span_mul_eq_span_mul_of_isTotallyPositive_mk'
    q I J hb hmk hxpos habcop hbcop hprod

/-- A chosen denominator-coprime `mk'` representative of the totally positive
principal multiplier in a narrow-fiber relation compares the raw signed-factor
characters. -/
theorem genusCharacterOfSignedFactorRaw_eq_of_denominator_coprime_mk'_of_mul_toPrincipalIdeal_eq
    {D : ℤ} [Fact (Squarefree D)] [Fact (D ≠ 1)]
    (q : {q // q ∈ signedPrimeDiscriminantFactors D})
    (I J : signedFactorCoprimeIdealSubmonoid D q)
    {x : (FractionRing (NumberField.RingOfIntegers (Qsqrtd (D : ℚ))))ˣ}
    (hxpos : NarrowClassGroup.IsTotallyPositive
      (x : FractionRing (NumberField.RingOfIntegers (Qsqrtd (D : ℚ)))))
    (hJ : FractionalIdeal.mk0
        (FractionRing (NumberField.RingOfIntegers (Qsqrtd (D : ℚ))))
        (signedFactorCoprimeIdealNonzeroMonoidHom D q I) *
      toPrincipalIdeal (NumberField.RingOfIntegers (Qsqrtd (D : ℚ)))
        (FractionRing (NumberField.RingOfIntegers (Qsqrtd (D : ℚ)))) x =
      FractionalIdeal.mk0
        (FractionRing (NumberField.RingOfIntegers (Qsqrtd (D : ℚ))))
        (signedFactorCoprimeIdealNonzeroMonoidHom D q J))
    {a b : NumberField.RingOfIntegers (Qsqrtd (D : ℚ))}
    (hb : b ≠ 0)
    (hmk : IsLocalization.mk'
        (FractionRing (NumberField.RingOfIntegers (Qsqrtd (D : ℚ)))) a
        ⟨b, mem_nonZeroDivisors_iff_ne_zero.mpr hb⟩ =
      (x : FractionRing (NumberField.RingOfIntegers (Qsqrtd (D : ℚ)))))
    (hbcop : Nat.Coprime
      (Ideal.absNorm (Ideal.span
        ({b} : Set (NumberField.RingOfIntegers (Qsqrtd (D : ℚ)))))) q.1.natAbs) :
    genusCharacterOfSignedFactorRaw D q I =
      genusCharacterOfSignedFactorRaw D q J := by
  have hprod :
      Ideal.span ({a} : Set (NumberField.RingOfIntegers (Qsqrtd (D : ℚ)))) *
          (I : Ideal (NumberField.RingOfIntegers (Qsqrtd (D : ℚ)))) =
        Ideal.span ({b} : Set (NumberField.RingOfIntegers (Qsqrtd (D : ℚ)))) *
          (J : Ideal (NumberField.RingOfIntegers (Qsqrtd (D : ℚ)))) :=
    span_mul_eq_span_mul_of_mk'_eq_of_mul_toPrincipalIdeal_eq D q I J hJ hb hmk
  exact genusCharacterOfSignedFactorRaw_eq_of_exists_denominator_coprime_mk'
    q I J hxpos ⟨a, b, hb, hmk, hbcop, hprod⟩

/-- Denominator-avoidance input for the narrow-fiber comparison: if two integral
ideal representatives are both coprime to the signed factor and differ by a
principal fractional ideal, the multiplier admits an integral fraction
representative whose denominator remains coprime to that signed factor. -/
theorem exists_denominator_coprime_mk'_of_mul_toPrincipalIdeal_eq
    {D : ℤ} [Fact (Squarefree D)] [Fact (D ≠ 1)]
    (q : {q // q ∈ signedPrimeDiscriminantFactors D})
    (I J : signedFactorCoprimeIdealSubmonoid D q)
    {x : (FractionRing (NumberField.RingOfIntegers (Qsqrtd (D : ℚ))))ˣ}
    (hJ : FractionalIdeal.mk0
        (FractionRing (NumberField.RingOfIntegers (Qsqrtd (D : ℚ))))
        (signedFactorCoprimeIdealNonzeroMonoidHom D q I) *
      toPrincipalIdeal (NumberField.RingOfIntegers (Qsqrtd (D : ℚ)))
        (FractionRing (NumberField.RingOfIntegers (Qsqrtd (D : ℚ)))) x =
      FractionalIdeal.mk0
        (FractionRing (NumberField.RingOfIntegers (Qsqrtd (D : ℚ))))
        (signedFactorCoprimeIdealNonzeroMonoidHom D q J)) :
    ∃ a b : NumberField.RingOfIntegers (Qsqrtd (D : ℚ)), ∃ hb : b ≠ 0,
      IsLocalization.mk'
          (FractionRing (NumberField.RingOfIntegers (Qsqrtd (D : ℚ)))) a
          ⟨b, mem_nonZeroDivisors_iff_ne_zero.mpr hb⟩ =
        (x : FractionRing (NumberField.RingOfIntegers (Qsqrtd (D : ℚ)))) ∧
      Nat.Coprime
        (Ideal.absNorm (Ideal.span
          ({b} : Set (NumberField.RingOfIntegers (Qsqrtd (D : ℚ)))))) q.1.natAbs := by
  let R := NumberField.RingOfIntegers (Qsqrtd (D : ℚ))
  let K := FractionRing R
  let b : R := Ideal.absNorm (I : Ideal R)
  have hbI : b ∈ (I : Ideal R) := by
    simpa [b, R] using Ideal.absNorm_mem (I : Ideal R)
  have hb_ne : b ≠ 0 := by
    have hI_norm_ne : Ideal.absNorm (I : Ideal R) ≠ 0 :=
      absNorm_ne_zero_of_mem_signedFactorCoprimeIdealSubmonoid D q I
    dsimp [b]
    exact Nat.cast_ne_zero.mpr hI_norm_ne
  have hfrac : FractionalIdeal.spanSingleton (nonZeroDivisors R) (x : K) *
        ((signedFactorCoprimeIdealNonzeroMonoidHom D q I : Ideal R) :
          FractionalIdeal (nonZeroDivisors R) K) =
      ((signedFactorCoprimeIdealNonzeroMonoidHom D q J : Ideal R) :
        FractionalIdeal (nonZeroDivisors R) K) := by
    have hJ_val := congrArg
      (fun U : (FractionalIdeal (nonZeroDivisors R) K)ˣ =>
          (U : FractionalIdeal (nonZeroDivisors R) K)) hJ
    simpa [R, K, coe_toPrincipalIdeal, mul_comm] using hJ_val
  have hb_mem_frac :
      algebraMap R K b ∈
        ((signedFactorCoprimeIdealNonzeroMonoidHom D q I : Ideal R) :
          FractionalIdeal (nonZeroDivisors R) K) :=
    FractionalIdeal.mem_coeIdeal_of_mem (nonZeroDivisors R) hbI
  have hxb_mem :
      (x : K) * algebraMap R K b ∈
        ((signedFactorCoprimeIdealNonzeroMonoidHom D q J : Ideal R) :
          FractionalIdeal (nonZeroDivisors R) K) := by
    rw [← hfrac]
    exact FractionalIdeal.mem_singleton_mul.mpr ⟨algebraMap R K b, hb_mem_frac, rfl⟩
  rcases (FractionalIdeal.mem_coeIdeal (S := nonZeroDivisors R)).mp hxb_mem with
    ⟨a, _haJ, ha⟩
  refine ⟨a, b, hb_ne, ?_, ?_⟩
  · rw [IsLocalization.mk'_eq_iff_eq_mul]
    simpa using ha
  · have hb_norm_coprime :
        Nat.Coprime (Ideal.absNorm (I : Ideal R)) q.1.natAbs := I.property
    have hb_span :
        Ideal.absNorm (Ideal.span ({b} : Set R)) =
          Ideal.absNorm (I : Ideal R) ^ 2 := by
      simpa [b, R] using
        (RingOfIntegers.absNorm_span_intCast (d := D)
          (n := (Ideal.absNorm (I : Ideal R) : ℤ)))
    rw [hb_span]
    exact hb_norm_coprime.pow_left 2

/-- Well-definedness input for signed-factor genus characters: the raw Kronecker
value is constant on fibers of the restricted narrow class-group map. -/
theorem genusCharacterOfSignedFactorRaw_eq_of_narrowMk0OnSignedFactorCoprimeIdeals_eq
      (q : {q // q ∈ signedPrimeDiscriminantFactors d})
      (I J : signedFactorCoprimeIdealSubmonoid d q)
      (hIJ : narrowMk0OnSignedFactorCoprimeIdeals d q I =
        narrowMk0OnSignedFactorCoprimeIdeals d q J) :
      genusCharacterOfSignedFactorRaw d q I = genusCharacterOfSignedFactorRaw d q J := by
  rcases (narrowMk0OnSignedFactorCoprimeIdeals_eq_iff_exists_fraction_ring d q I J).mp hIJ with
    ⟨x, hxpos, hxIJ⟩
  rcases exists_denominator_coprime_mk'_of_mul_toPrincipalIdeal_eq q I J hxIJ with
    ⟨a, b, hb, hmk, hbcop⟩
  exact genusCharacterOfSignedFactorRaw_eq_of_denominator_coprime_mk'_of_mul_toPrincipalIdeal_eq
    q I J hxpos hxIJ hb hmk hbcop

/-- The genus character attached to one signed prime-discriminant factor.
On a class represented by an ideal `I` whose norm is coprime to `q`, this should
evaluate as `kroneckerSymNat q.1 (Ideal.absNorm I)`. -/
noncomputable def genusCharacterOfSignedFactor
      (q : {q // q ∈ signedPrimeDiscriminantFactors d}) :
      Cl⁺(d) →* ℤˣ :=
  genusCharacterOfSignedFactorDescent d q
    (narrowMk0OnSignedFactorCoprimeIdeals_surjective d q)
    (genusCharacterOfSignedFactorRaw_eq_of_narrowMk0OnSignedFactorCoprimeIdeals_eq d q)

/-- The descended signed-factor character evaluates as the raw Kronecker character
on a narrow class represented by an ideal whose norm is coprime to that factor. -/
theorem genusCharacterOfSignedFactor_apply_narrowMk0OnSignedFactorCoprimeIdeals
      (q : {q // q ∈ signedPrimeDiscriminantFactors d})
      (I : signedFactorCoprimeIdealSubmonoid d q) :
      genusCharacterOfSignedFactor d q (narrowMk0OnSignedFactorCoprimeIdeals d q I) =
        genusCharacterOfSignedFactorRaw d q I := by
  simpa [genusCharacterOfSignedFactor] using
    genusCharacterOfSignedFactorDescent_apply_narrowMk0OnSignedFactorCoprimeIdeals
      d q (narrowMk0OnSignedFactorCoprimeIdeals_surjective d q)
      (genusCharacterOfSignedFactorRaw_eq_of_narrowMk0OnSignedFactorCoprimeIdeals_eq d q) I

/-- If a nonzero integral ideal is coprime to every signed factor, then each
descended signed-factor character on its narrow class is computed by the raw
Kronecker character at that ideal. -/
theorem genusCharacterOfSignedFactor_apply_mk0_of_mem_signedFactorsCoprimeIdealSubmonoid
      (q : {q // q ∈ signedPrimeDiscriminantFactors d})
      (I : (Ideal (NumberField.RingOfIntegers (Qsqrtd (d : ℚ))))⁰)
      (hI : (I : Ideal (NumberField.RingOfIntegers (Qsqrtd (d : ℚ)))) ∈
        signedFactorsCoprimeIdealSubmonoid d) :
      genusCharacterOfSignedFactor d q (NarrowClassGroup.mk0 I) =
        genusCharacterOfSignedFactorRaw d q ⟨I, hI q⟩ := by
  let J : signedFactorCoprimeIdealSubmonoid d q := ⟨I, hI q⟩
  have hJ :
      narrowMk0OnSignedFactorCoprimeIdeals d q J = NarrowClassGroup.mk0 I := by
    simp [J, narrowMk0OnSignedFactorCoprimeIdeals, signedFactorCoprimeIdealNonzeroMonoidHom]
  rw [← hJ]
  simpa [J] using genusCharacterOfSignedFactor_apply_narrowMk0OnSignedFactorCoprimeIdeals d q J

/-- If an ideal is coprime to every signed prime-discriminant factor, then its
absolute norm has field-discriminant Kronecker value `1`. -/
theorem kroneckerSymNat_discr_absNorm_eq_one_of_mem_signedFactorsCoprimeIdealSubmonoid
      (I : (Ideal (NumberField.RingOfIntegers (Qsqrtd (d : ℚ))))⁰)
      (hI : (I : Ideal (NumberField.RingOfIntegers (Qsqrtd (d : ℚ)))) ∈
        signedFactorsCoprimeIdealSubmonoid d) :
      kroneckerSymNat (NumberField.discr (Qsqrtd (d : ℚ)))
        (Ideal.absNorm (I : Ideal (NumberField.RingOfIntegers (Qsqrtd (d : ℚ))))) = 1 := by
  have hI_ne : (I : Ideal (NumberField.RingOfIntegers (Qsqrtd (d : ℚ)))) ≠ ⊥ := by
    have hI_nonzero := I.2
    rw [mem_nonZeroDivisors_iff_ne_zero] at hI_nonzero
    rwa [Ideal.zero_eq_bot] at hI_nonzero
  refine Splitting.kroneckerSymNat_discr_absNorm_eq_one_of_forall_prime_dvd_not_isRamifiedIn
    d hI_ne ?_
  intro p hp_prime hp_dvd hram
  have hp_ram : p ∈ ramifiedPrimes d :=
    (mem_ramifiedPrimes_iff_isRamifiedIn d p).mpr ⟨hp_prime, hram⟩
  let q : {q // q ∈ signedPrimeDiscriminantFactors d} :=
    ⟨primeDiscriminantFactor d p,
      mem_signedPrimeDiscriminantFactors_of_mem_ramifiedPrimes d hp_ram⟩
  have hcop := hI q
  change Nat.Coprime
    (Ideal.absNorm (I : Ideal (NumberField.RingOfIntegers (Qsqrtd (d : ℚ)))))
      (primeDiscriminantFactor d p).natAbs at hcop
  have hp_dvd_q : p ∣ (primeDiscriminantFactor d p).natAbs :=
    dvd_natAbs_primeDiscriminantFactor_of_mem_ramifiedPrimes hp_ram
  have hp_dvd_one : p ∣ 1 := by
    have hp_dvd_gcd :
        p ∣ Nat.gcd
          (Ideal.absNorm (I : Ideal (NumberField.RingOfIntegers (Qsqrtd (d : ℚ)))))
          (primeDiscriminantFactor d p).natAbs :=
      Nat.dvd_gcd hp_dvd hp_dvd_q
    have hgcd :
        Nat.gcd
          (Ideal.absNorm (I : Ideal (NumberField.RingOfIntegers (Qsqrtd (d : ℚ)))))
          (primeDiscriminantFactor d p).natAbs = 1 := hcop
    rwa [hgcd] at hp_dvd_gcd
  have hp_le_one : p ≤ 1 := Nat.le_of_dvd (by norm_num) hp_dvd_one
  have hp_two_le : 2 ≤ p := hp_prime.two_le
  omega

/-- Pure Kronecker product formula on a common representative: if one nonzero
integral ideal is coprime to every signed factor, the product of the
signed-factor Kronecker values is `1`. -/
theorem signedFactorKroneckerProduct_one_of_mem_signedFactorsCoprimeIdealSubmonoid
      (I : (Ideal (NumberField.RingOfIntegers (Qsqrtd (d : ℚ))))⁰)
      (hI : (I : Ideal (NumberField.RingOfIntegers (Qsqrtd (d : ℚ)))) ∈
        signedFactorsCoprimeIdealSubmonoid d) :
      Finset.univ.prod (fun q : {q // q ∈ signedPrimeDiscriminantFactors d} =>
        kroneckerSymNat q.1
          (Ideal.absNorm (I : Ideal (NumberField.RingOfIntegers (Qsqrtd (d : ℚ)))))) = 1 := by
  let n := Ideal.absNorm (I : Ideal (NumberField.RingOfIntegers (Qsqrtd (d : ℚ))))
  have hn : n ≠ 0 := by
    have hI_nonzero := I.2
    rw [mem_nonZeroDivisors_iff_ne_zero] at hI_nonzero
    dsimp [n]
    intro hzero
    rw [Ideal.absNorm_eq_zero_iff] at hzero
    rw [Ideal.zero_eq_bot] at hI_nonzero
    exact hI_nonzero hzero
  have hdisc :=
    kroneckerSymNat_discr_absNorm_eq_one_of_mem_signedFactorsCoprimeIdealSubmonoid d I hI
  change Finset.univ.prod (fun q : {q // q ∈ signedPrimeDiscriminantFactors d} =>
      kroneckerSymNat q.1 n) = 1
  calc
    Finset.univ.prod (fun q : {q // q ∈ signedPrimeDiscriminantFactors d} =>
        kroneckerSymNat q.1 n) =
        (signedPrimeDiscriminantFactors d).attach.prod (fun q => kroneckerSymNat q.1 n) := by
      simp
    _ = kroneckerSymNat ((signedPrimeDiscriminantFactors d).attach.prod fun q => q.1) n := by
      rw [← kroneckerSymNat_prod_left _ _ hn]
    _ = kroneckerSymNat ((signedPrimeDiscriminantFactors d).prod id) n := by
      congr 1
      exact Finset.prod_attach (signedPrimeDiscriminantFactors d) id
    _ = kroneckerSymNat (RingOfIntegers.discrFormula d) n := by
      rw [prod_signedPrimeDiscriminantFactors_eq_discrFormula d]
    _ = kroneckerSymNat (NumberField.discr (Qsqrtd (d : ℚ))) n := by
      rw [← RingOfIntegers.discr_formula d]
    _ = 1 := by
      simpa [n] using hdisc

/-- The raw unit-valued product formula follows from the corresponding integer
Kronecker product formula. -/
theorem signedFactorRawCharacters_product_one_of_kroneckerProduct
      (I : (Ideal (NumberField.RingOfIntegers (Qsqrtd (d : ℚ))))⁰)
      (hI : (I : Ideal (NumberField.RingOfIntegers (Qsqrtd (d : ℚ)))) ∈
        signedFactorsCoprimeIdealSubmonoid d)
      (hprod : Finset.univ.prod (fun q : {q // q ∈ signedPrimeDiscriminantFactors d} =>
        kroneckerSymNat q.1
          (Ideal.absNorm (I : Ideal (NumberField.RingOfIntegers (Qsqrtd (d : ℚ)))))) = 1) :
      Finset.univ.prod (fun q : {q // q ∈ signedPrimeDiscriminantFactors d} =>
        genusCharacterOfSignedFactorRaw d q ⟨I, hI q⟩) = 1 := by
  ext
  simpa using hprod

/-- Raw Kronecker product formula on a common representative: if one nonzero
integral ideal is coprime to every signed factor, the product of the raw
signed-factor values is `1`. -/
theorem signedFactorRawCharacters_product_one_of_mem_signedFactorsCoprimeIdealSubmonoid
      (I : (Ideal (NumberField.RingOfIntegers (Qsqrtd (d : ℚ))))⁰)
      (hI : (I : Ideal (NumberField.RingOfIntegers (Qsqrtd (d : ℚ)))) ∈
        signedFactorsCoprimeIdealSubmonoid d) :
      Finset.univ.prod (fun q : {q // q ∈ signedPrimeDiscriminantFactors d} =>
        genusCharacterOfSignedFactorRaw d q ⟨I, hI q⟩) = 1 :=
  signedFactorRawCharacters_product_one_of_kroneckerProduct d I hI
    (signedFactorKroneckerProduct_one_of_mem_signedFactorsCoprimeIdealSubmonoid d I hI)

/-- Product formula input for genus characters: the signed-factor characters
attached to a narrow ideal class have product `1`. -/
theorem genusCharacterMap_product_one
      (C : Cl⁺(d)) :
      Finset.univ.prod (fun q : {q // q ∈ signedPrimeDiscriminantFactors d} =>
        genusCharacterOfSignedFactor d q C) = 1 := by
  rcases exists_signedFactorsCoprime_representative d C with ⟨I, hC, hI⟩
  rw [← hC]
  calc
    Finset.univ.prod (fun q : {q // q ∈ signedPrimeDiscriminantFactors d} =>
        genusCharacterOfSignedFactor d q (NarrowClassGroup.mk0 I)) =
        Finset.univ.prod (fun q : {q // q ∈ signedPrimeDiscriminantFactors d} =>
          genusCharacterOfSignedFactorRaw d q ⟨I, hI q⟩) := by
      apply Finset.prod_congr rfl
      intro q hq
      exact genusCharacterOfSignedFactor_apply_mk0_of_mem_signedFactorsCoprimeIdealSubmonoid
        d q I hI
    _ = 1 :=
      signedFactorRawCharacters_product_one_of_mem_signedFactorsCoprimeIdealSubmonoid d I hI

/-- The genus-character map from the narrow class group to the product-one sign
relation subgroup. This is the main construction boundary for genus theory. -/
noncomputable def genusCharacterMap :
    Cl⁺(d) →* genusCharacterTargetRelation d := by
  refine
    { toFun := fun C =>
        ⟨fun q => genusCharacterOfSignedFactor d q C, by
          exact genusCharacterMap_product_one d C⟩
      map_one' := by
        ext q
        simp
      map_mul' := by
        intro C D
        ext q
        simp }

/-- The coordinate of `genusCharacterMap d C` at a signed prime-discriminant
factor is the corresponding signed-factor genus character. -/
@[simp]
theorem genusCharacterMap_apply
    (C : Cl⁺(d))
    (q : {q // q ∈ signedPrimeDiscriminantFactors d}) :
    (genusCharacterMap d C : genusCharacterTarget d) q =
      genusCharacterOfSignedFactor d q C := by
  rfl

/-- Coordinate form of `genusCharacterMap` on a narrow class represented by an
ideal coprime to every signed prime-discriminant factor. -/
theorem genusCharacterMap_apply_mk0_of_mem_signedFactorsCoprimeIdealSubmonoid
      (I : (Ideal (NumberField.RingOfIntegers (Qsqrtd (d : ℚ))))⁰)
      (hI : (I : Ideal (NumberField.RingOfIntegers (Qsqrtd (d : ℚ)))) ∈
        signedFactorsCoprimeIdealSubmonoid d)
      (q : {q // q ∈ signedPrimeDiscriminantFactors d}) :
      (genusCharacterMap d (NarrowClassGroup.mk0 I) : genusCharacterTarget d) q =
        genusCharacterOfSignedFactorRaw d q ⟨I, hI q⟩ := by
  rw [genusCharacterMap_apply]
  exact genusCharacterOfSignedFactor_apply_mk0_of_mem_signedFactorsCoprimeIdealSubmonoid d q I hI

end GenusTheory
end ClassGroup
end QuadraticNumberFields
