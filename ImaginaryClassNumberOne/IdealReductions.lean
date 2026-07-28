/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/
import Mathlib.NumberTheory.Multiplicity
import Mathlib.NumberTheory.NumberField.ClassNumber
import QNFMathlib.Data.Nat.Squarefree
import QuadraticNumberFields.QuadraticField.Basic
import QuadraticNumberFields.RingOfIntegers.Norm
import QuadraticNumberFields.Splitting.Factorization
import QuadraticNumberFields.Splitting.Qsqrtd.Kronecker
import QuadraticNumberFields.Splitting.Qsqrtd.Two

/-!
# Ideal-Theoretic Reductions for the Heegner Class-Number-One Problem

This file collects small ideal-first reductions used in the class-number-one
direction of the Baker--Heegner--Stark theorem.  The first reduction isolates
the elementary norm obstruction in the even-discriminant branch and the
odd-discriminant prime-shape reduction used by the Baker-Heegner-Stark forward
direction.
-/

open scoped NumberField

namespace QuadraticNumberFields
namespace Heegner

attribute [-instance] DivisionRing.toRatAlgebra

private theorem int_sq_ne_nat_prime {p : ℕ} (hp : p.Prime) (a : ℤ) :
    a ^ 2 ≠ (p : ℤ) := by
  intro h
  have hp_prime_int : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have hsq : IsSquare (p : ℤ) := ⟨a, by simpa [pow_two] using h.symm⟩
  exact hp_prime_int.not_isSquare hsq

private theorem int_sq_ne_two (a : ℤ) : a ^ 2 ≠ 2 := by
  exact int_sq_ne_nat_prime Nat.prime_two a

private theorem nat_eq_two_of_sq_eq_four {n : ℕ} (h : 4 = n ^ 2) (hn : n ≠ 0) :
    n = 2 := by
  have hnle : n ≤ 4 := by nlinarith [sq_nonneg (n : ℤ)]
  interval_cases n <;> simp_all

private theorem eq_neg_one_or_eq_neg_two_of_zsqrtd_norm_eq_two
    {d : ℤ} (hdneg : d < 0) {z : Zsqrtd d} (hnorm : Zsqrtd.norm z = 2) :
    d = -1 ∨ d = -2 := by
  have hcoord : z.re ^ 2 - d * z.im ^ 2 = 2 := by
    simpa [RingOfIntegers.norm_zsqrtd] using hnorm
  by_cases him : z.im = 0
  · have hre_sq : z.re ^ 2 = 2 := by
      simpa [him] using hcoord
    exact False.elim (int_sq_ne_two z.re hre_sq)
  · have him_sq_pos : 0 < z.im ^ 2 := sq_pos_of_ne_zero him
    have hnegd_le : -d ≤ 2 := by nlinarith [sq_nonneg z.re, him_sq_pos]
    omega

private theorem eq_neg_seven_of_zOnePlusSqrtOverTwo_norm_eq_two
    {k d : ℤ} (hdk : d = 1 + 4 * k) (hdneg : d < 0) (hd8 : d % 8 = 1)
    {z : ZOnePlusSqrtdOverTwo k} (hnorm : QuadraticAlgebra.norm z = 2) :
    d = -7 := by
  have hcoord : z.re ^ 2 + z.re * z.im - k * z.im ^ 2 = 2 := by
    cases z
    simpa [ZOnePlusSqrtdOverTwo.norm_mk] using hnorm
  have hquad : (2 * z.re + z.im) ^ 2 - d * z.im ^ 2 = 8 := by
    rw [hdk]
    nlinarith
  by_cases him : z.im = 0
  · have hre_sq : z.re ^ 2 = 2 := by
      rw [him] at hcoord
      simpa using hcoord
    exact False.elim (int_sq_ne_two z.re hre_sq)
  · have him_sq_pos : 0 < z.im ^ 2 := sq_pos_of_ne_zero him
    have him_sq_ge_one : 1 ≤ z.im ^ 2 := by omega
    have hnegd_pos : 0 < -d := by omega
    have hnegd_le_prod : -d ≤ (-d) * z.im ^ 2 := by nlinarith
    have hprod_le : (-d) * z.im ^ 2 ≤ 8 := by nlinarith [sq_nonneg (2 * z.re + z.im)]
    have hnegd_le : -d ≤ 8 := le_trans hnegd_le_prod hprod_le
    omega

/-- In the `d % 4 ≠ 1` branch of an imaginary quadratic field, an algebraic integer
of norm absolute value `2` can exist only for `d = -1` or `d = -2`. -/
theorem eq_neg_one_or_eq_neg_two_of_exists_absNorm_eq_two
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] (hdneg : d < 0) (hd4 : d % 4 ≠ 1)
    (h : ∃ α : 𝓞 (Qsqrtd (d : ℚ)), (Algebra.norm ℤ α).natAbs = 2) :
    d = -1 ∨ d = -2 := by
  rcases h with ⟨α, hα⟩
  have hnorm_nonneg : 0 ≤ Algebra.norm ℤ α :=
    RingOfIntegers.algebraNorm_nonneg_of_neg d hdneg α
  have hnorm_eq_two : Algebra.norm ℤ α = 2 := by
    have hnat := Int.natAbs_of_nonneg hnorm_nonneg
    omega
  have hz_norm :
      Zsqrtd.norm
        (RingOfIntegers.ringOfIntegers_equiv_zsqrtd_of_mod_four_ne_one d hd4 α) = 2 := by
    rw [← RingOfIntegers.algebraNorm_eq_zsqrtd_norm_of_mod_four_ne_one d hd4 α]
    exact hnorm_eq_two
  exact eq_neg_one_or_eq_neg_two_of_zsqrtd_norm_eq_two hdneg hz_norm

/-- In the `d % 8 = 1` split half-integral branch, an algebraic integer of norm
absolute value `2` can exist only for `d = -7`. -/
theorem eq_neg_seven_of_exists_absNorm_eq_two_of_mod_eight_eq_one
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] (hdneg : d < 0) (hd8 : d % 8 = 1)
    (h : ∃ α : 𝓞 (Qsqrtd (d : ℚ)), (Algebra.norm ℤ α).natAbs = 2) :
    d = -7 := by
  rcases h with ⟨α, hα⟩
  have hnorm_nonneg : 0 ≤ Algebra.norm ℤ α :=
    RingOfIntegers.algebraNorm_nonneg_of_neg d hdneg α
  have hnorm_eq_two : Algebra.norm ℤ α = 2 := by
    have hnat := Int.natAbs_of_nonneg hnorm_nonneg
    omega
  let k : ℤ := d / 4
  have hdk : d = 1 + 4 * k := by
    dsimp [k]
    omega
  have hz_norm :
      QuadraticAlgebra.norm
        (RingOfIntegers.ringOfIntegers_equiv_zOnePlusSqrtOverTwo_of_eq d k hdk α) = 2 := by
    rw [← RingOfIntegers.algebraNorm_eq_zOnePlusSqrtOverTwo_norm_of_eq d k hdk α]
    exact hnorm_eq_two
  exact eq_neg_seven_of_zOnePlusSqrtOverTwo_norm_eq_two hdk hdneg hd8 hz_norm

/-- In the `d % 4 ≠ 1` branch, class number one forces a norm-`2` algebraic
integer.  The proof uses only ideal theory: `(2)` ramifies, so its lift is
`P ^ 2`; class number one makes `P` principal, and `absNorm P = 2` gives a
principal generator of algebra norm absolute value `2`. -/
theorem exists_algebraNorm_natAbs_eq_two_of_classNumber_eq_one_of_mod_four_ne_one
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] (hd4 : d % 4 ≠ 1)
    (hclass : NumberField.classNumber (Qsqrtd (d : ℚ)) = 1) :
    ∃ α : 𝓞 (Qsqrtd (d : ℚ)), (Algebra.norm ℤ α).natAbs = 2 := by
  let O := 𝓞 (Qsqrtd (d : ℚ))
  let p : Ideal ℤ := Ideal.span ({(2 : ℤ)} : Set ℤ)
  have hchar : ringChar ℤ ≠ 2 := by simp [ringChar.eq_zero]
  have hpbot : p ≠ ⊥ := by
    dsimp [p]
    intro h
    have htwo : (2 : ℤ) = 0 := Ideal.span_singleton_eq_bot.mp h
    norm_num at htwo
  haveI : p.IsMaximal := by
    dsimp [p]
    exact PrincipalIdealRing.isMaximal_of_irreducible
      ((Nat.prime_iff_prime_int.mp Nat.prime_two).irreducible)
  have hram : Ideal.IsRamifiedIn p O := by
    simpa [p, O] using Splitting.isRamified_two_of_mod_four_ne_one d hd4
  obtain ⟨P, hPover, hmap⟩ := Ideal.map_eq_sq_of_isRamifiedIn p O hchar hpbot hram
  have hP_principal : P.IsPrincipal := by
    have hPID : IsPrincipalIdealRing O :=
      (NumberField.classNumber_eq_one_iff (K := Qsqrtd (d : ℚ))).mp hclass
    letI : IsPrincipalIdealRing O := hPID
    exact IsPrincipalIdealRing.principal P
  obtain ⟨α, _hspan, hnorm⟩ :=
    RingOfIntegers.absNorm_eq_natAbs_algebraNorm_of_isPrincipal (d := d) hP_principal
  refine ⟨α, ?_⟩
  have hP_abs : Ideal.absNorm P = 2 := by
    have hnorm_map := congrArg Ideal.absNorm hmap
    have hleft : Ideal.absNorm (Ideal.map (algebraMap ℤ O) p) = 4 := by
      dsimp [p]
      rw [Ideal.map_span, Set.image_singleton]
      simpa using RingOfIntegers.absNorm_span_intCast (d := d) 2
    have hright : Ideal.absNorm (P ^ 2) = Ideal.absNorm P ^ 2 := by
      simp
    rw [hleft, hright] at hnorm_map
    have hPne : Ideal.absNorm P ≠ 0 := by
      rw [Ne, Ideal.absNorm_eq_zero_iff]
      intro hPbot
      letI : P.LiesOver p := hPover.2
      have hover : p = Ideal.under ℤ P := Ideal.LiesOver.over
      have hunder : Ideal.under ℤ P = ⊥ := by
        rw [hPbot]
        exact Ideal.comap_bot_of_injective (algebraMap ℤ O) (RingHom.injective_int _)
      exact hpbot (hover.trans hunder)
    exact nat_eq_two_of_sq_eq_four hnorm_map hPne
  exact hnorm.symm.trans hP_abs

/-- In the `d % 8 = 1` split branch, class number one forces a norm-`2`
algebraic integer.  The proof uses only ideal theory: a prime above `2` has
residue degree one, class number one makes it principal, and its absolute norm
is `2`. -/
theorem exists_algebraNorm_natAbs_eq_two_of_classNumber_eq_one_of_mod_eight_eq_one
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] (hd8 : d % 8 = 1)
    (hclass : NumberField.classNumber (Qsqrtd (d : ℚ)) = 1) :
    ∃ α : 𝓞 (Qsqrtd (d : ℚ)), (Algebra.norm ℤ α).natAbs = 2 := by
  let O := 𝓞 (Qsqrtd (d : ℚ))
  let p : Ideal ℤ := Ideal.span ({(2 : ℤ)} : Set ℤ)
  have hchar : ringChar ℤ ≠ 2 := by simp [ringChar.eq_zero]
  have hpbot : p ≠ ⊥ := by
    dsimp [p]
    intro h
    have htwo : (2 : ℤ) = 0 := Ideal.span_singleton_eq_bot.mp h
    norm_num at htwo
  haveI : p.IsMaximal := by
    dsimp [p]
    exact PrincipalIdealRing.isMaximal_of_irreducible
      ((Nat.prime_iff_prime_int.mp Nat.prime_two).irreducible)
  have hsplit : Ideal.IsSplitIn p O := by
    simpa [p, O] using Splitting.isSplit_two_of_mod_eight_eq_one (d := d) hd8
  obtain ⟨P, hP, _P2, _hP2, _hne, _hmap⟩ :=
    Ideal.map_eq_of_isSplitIn p O hchar hpbot hsplit
  have hPover_span : P.LiesOver (Ideal.span ({(2 : ℤ)} : Set ℤ)) := by
    simpa [p] using hP.2
  letI : P.LiesOver (Ideal.span ({(2 : ℤ)} : Set ℤ)) := hPover_span
  have hfP : P.inertiaDeg ℤ = 1 := by
    letI := Ring.instAlgebraFractionRing
    letI := IsIntegralClosure.MulSemiringAction ℤ (FractionRing ℤ) (FractionRing O) O
    letI := Algebra.IsQuadraticExtension.isGaloisGroup (R := ℤ) (S := O) hchar
    have hf := Ideal.inertiaDegIn_eq_of_mem p O Gal(FractionRing O / FractionRing ℤ) hP
    have hf1 : Ideal.inertiaDegIn p O = 1 := hsplit.2
    rw [hf1] at hf
    simpa [p] using hf.symm
  have hP_principal : P.IsPrincipal := by
    have hPID : IsPrincipalIdealRing O :=
      (NumberField.classNumber_eq_one_iff (K := Qsqrtd (d : ℚ))).mp hclass
    letI : IsPrincipalIdealRing O := hPID
    exact IsPrincipalIdealRing.principal P
  obtain ⟨α, _hspan, hnorm⟩ :=
    RingOfIntegers.absNorm_eq_natAbs_algebraNorm_of_isPrincipal (d := d) hP_principal
  refine ⟨α, ?_⟩
  have hP_abs : Ideal.absNorm P = 2 := by
    letI : P.IsPrime := hP.1
    have hnormP := Ideal.pow_inertiaDeg 2 P
    rw [hfP] at hnormP
    norm_num at hnormP
    exact hnormP.symm
  exact hnorm.symm.trans hP_abs

/-- If a rational prime `q` divides the squarefree parameter `d`, then class
number one forces an algebraic integer of norm absolute value `q`.

This is the ramified-prime variant of the `2`-adic reductions above: `(q)`
ramifies, the unique prime above `q` is principal when the class number is one,
and the ramified prime-ideal norm is `q`. -/
theorem exists_algebraNorm_natAbs_eq_prime_of_classNumber_eq_one_of_dvd
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)]
    (q : ℕ) [Fact q.Prime] (hqd : (q : ℤ) ∣ d)
    (hclass : NumberField.classNumber (Qsqrtd (d : ℚ)) = 1) :
    ∃ α : 𝓞 (Qsqrtd (d : ℚ)), (Algebra.norm ℤ α).natAbs = q := by
  let O := 𝓞 (Qsqrtd (d : ℚ))
  let p : Ideal ℤ := Ideal.span ({(q : ℤ)} : Set ℤ)
  have hchar : ringChar ℤ ≠ 2 := by simp [ringChar.eq_zero]
  have hpbot : p ≠ ⊥ := by
    dsimp [p]
    intro h
    have hq0 : (q : ℤ) = 0 := Ideal.span_singleton_eq_bot.mp h
    exact (Fact.out : Nat.Prime q).ne_zero (Nat.cast_eq_zero.mp hq0)
  haveI : p.IsMaximal := by
    dsimp [p]
    exact PrincipalIdealRing.isMaximal_of_irreducible
      ((Nat.prime_iff_prime_int.mp (Fact.out : Nat.Prime q)).irreducible)
  have hram : Ideal.IsRamifiedIn p O := by
    dsimp [p, O]
    exact Splitting.isRamified_of_dvd d q hqd
  obtain ⟨P, hPover, _hmap⟩ := Ideal.map_eq_sq_of_isRamifiedIn p O hchar hpbot hram
  have hP_principal : P.IsPrincipal := by
    have hPID : IsPrincipalIdealRing O :=
      (NumberField.classNumber_eq_one_iff (K := Qsqrtd (d : ℚ))).mp hclass
    letI : IsPrincipalIdealRing O := hPID
    exact IsPrincipalIdealRing.principal P
  obtain ⟨α, _hspan, hnorm⟩ :=
    RingOfIntegers.absNorm_eq_natAbs_algebraNorm_of_isPrincipal (d := d) hP_principal
  refine ⟨α, ?_⟩
  have hP_abs : Ideal.absNorm P = q := by
    letI : P.IsPrime := hPover.1
    have hP_lies : P.LiesOver (Ideal.span ({(q : ℤ)} : Set ℤ)) := by
      simpa [p] using hPover.2
    letI : P.LiesOver (Ideal.span ({(q : ℤ)} : Set ℤ)) := hP_lies
    have hram' :
        Ideal.IsRamifiedIn (Ideal.span ({(q : ℤ)} : Set ℤ)) (𝓞 (Qsqrtd (d : ℚ))) := by
      simpa [p, O] using hram
    exact Splitting.absNorm_eq_prime_of_liesOver_of_isRamifiedIn d q hram'
  exact hnorm.symm.trans hP_abs

private theorem false_of_zOnePlusSqrtOverTwo_norm_eq_prime_of_four_mul_lt
    {k d : ℤ} (hdk : d = 1 + 4 * k) (hdneg : d < 0)
    {q : ℕ} (hq : q.Prime) (hsmall : 4 * (q : ℤ) < -d + 1)
    {z : ZOnePlusSqrtdOverTwo k} (hnorm : QuadraticAlgebra.norm z = (q : ℤ)) :
    False := by
  have hcoord : z.re ^ 2 + z.re * z.im - k * z.im ^ 2 = (q : ℤ) := by
    cases z
    simpa [ZOnePlusSqrtdOverTwo.norm_mk] using hnorm
  have hquad : (2 * z.re + z.im) ^ 2 - d * z.im ^ 2 = 4 * (q : ℤ) := by
    rw [hdk]
    nlinarith
  by_cases him : z.im = 0
  · have hre_sq : z.re ^ 2 = (q : ℤ) := by
      rw [him] at hcoord
      simpa using hcoord
    exact int_sq_ne_nat_prime hq z.re hre_sq
  · have him_sq_pos : 0 < z.im ^ 2 := sq_pos_of_ne_zero him
    have him_sq_ge_one : 1 ≤ z.im ^ 2 := by omega
    have hnegd_pos : 0 < -d := by omega
    have hnegd_le_prod : -d ≤ (-d) * z.im ^ 2 := by nlinarith
    have hprod_le : (-d) * z.im ^ 2 ≤ 4 * (q : ℤ) := by
      nlinarith [sq_nonneg (2 * z.re + z.im)]
    have hnegd_le : -d ≤ 4 * (q : ℤ) := le_trans hnegd_le_prod hprod_le
    omega

/-- In the `d % 4 ≠ 1` branch of the imaginary class-number-one problem, the only
possibilities are the Gaussian and `√-2` fields. -/
theorem eq_neg_one_or_eq_neg_two_of_classNumber_eq_one_of_mod_four_ne_one
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] (hdneg : d < 0) (hd4 : d % 4 ≠ 1)
    (hclass : NumberField.classNumber (Qsqrtd (d : ℚ)) = 1) :
    d = -1 ∨ d = -2 :=
  eq_neg_one_or_eq_neg_two_of_exists_absNorm_eq_two d hdneg hd4
    (exists_algebraNorm_natAbs_eq_two_of_classNumber_eq_one_of_mod_four_ne_one d hd4 hclass)

/-- In the `d % 8 = 1` split half-integral branch of the imaginary
class-number-one problem, the only possibility is the `√-7` field. -/
theorem eq_neg_seven_of_classNumber_eq_one_of_mod_eight_eq_one
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] (hdneg : d < 0) (hd8 : d % 8 = 1)
    (hclass : NumberField.classNumber (Qsqrtd (d : ℚ)) = 1) :
    d = -7 :=
  eq_neg_seven_of_exists_absNorm_eq_two_of_mod_eight_eq_one d hdneg hd8
    (exists_algebraNorm_natAbs_eq_two_of_classNumber_eq_one_of_mod_eight_eq_one d hd8 hclass)

/-- In the odd fundamental-discriminant branch `d % 4 = 1`, class number one
forces the squarefree parameter to be a negative prime `-p` with `p ≡ 3 (mod 4)`.

The proof is ideal-theoretic. If `|d|` had more than one prime factor, the
general squarefree arithmetic lemma gives a ramified prime `q ∣ d` with
`4q < |d| + 1`. Class number one makes the prime above `q` principal, producing
an algebraic integer of norm `q`; the half-integral norm equation then contradicts
the smallness bound. -/
theorem classNumber_eq_one_imp_exists_prime_of_mod_four_eq_one
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] (hd : d < 0) (hd4 : d % 4 = 1)
    (hclass : NumberField.classNumber (Qsqrtd (d : ℚ)) = 1) :
    ∃ p : ℕ, p.Prime ∧ p % 4 = 3 ∧ d = -(p : ℤ) := by
  have hsq_nat : Squarefree d.natAbs := Int.squarefree_natAbs.mpr (Fact.out : Squarefree d)
  have hodd_int : Odd d := by
    rw [Int.odd_iff]
    omega
  have hodd_nat : Odd d.natAbs := Int.natAbs_odd.mpr hodd_int
  have hdnat : (d.natAbs : ℤ) = -d := Int.ofNat_natAbs_of_nonpos (by omega)
  have hgt : 1 < d.natAbs := by omega
  by_cases hprime : d.natAbs.Prime
  · refine ⟨d.natAbs, hprime, ?_, ?_⟩
    · omega
    · omega
  · obtain ⟨q, hqprime, hq_dvd_nat, hsmall_nat⟩ :=
      Nat.exists_prime_dvd_and_four_mul_lt_succ_of_squarefree_of_odd_of_not_prime
        hsq_nat hodd_nat hgt hprime
    haveI : Fact q.Prime := ⟨hqprime⟩
    have hq_dvd_d : (q : ℤ) ∣ d := by
      rw [← Int.dvd_natAbs]
      exact Int.natCast_dvd_natCast.mpr hq_dvd_nat
    obtain ⟨α, hαnorm_abs⟩ :=
      exists_algebraNorm_natAbs_eq_prime_of_classNumber_eq_one_of_dvd d q hq_dvd_d hclass
    have hnorm_nonneg : 0 ≤ Algebra.norm ℤ α :=
      RingOfIntegers.algebraNorm_nonneg_of_neg d hd α
    have hnorm_eq_q : Algebra.norm ℤ α = (q : ℤ) := by
      have hnat := Int.natAbs_of_nonneg hnorm_nonneg
      omega
    obtain ⟨k, hdk⟩ := RingOfIntegers.exists_k_of_mod_four_eq_one hd4
    have hz_norm :
        QuadraticAlgebra.norm
          (RingOfIntegers.ringOfIntegers_equiv_zOnePlusSqrtOverTwo_of_eq d k hdk α) =
            (q : ℤ) := by
      rw [← RingOfIntegers.algebraNorm_eq_zOnePlusSqrtOverTwo_norm_of_eq d k hdk α]
      exact hnorm_eq_q
    have hsmall_int : 4 * (q : ℤ) < -d + 1 := by omega
    exact False.elim
      (false_of_zOnePlusSqrtOverTwo_norm_eq_prime_of_four_mul_lt hdk hd hqprime
        hsmall_int hz_norm)

end Heegner
end QuadraticNumberFields
