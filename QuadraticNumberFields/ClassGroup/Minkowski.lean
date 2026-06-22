/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/

import Mathlib.NumberTheory.NumberField.ClassNumber
import QNFMathlib.RingTheory.DedekindDomain.Ideal
import QNFMathlib.RingTheory.Ideal.Norm.AbsNorm
import QuadraticNumberFields.ClassGroup.Basic
import QuadraticNumberFields.Qsqrtd.TotallyRealComplex
import QuadraticNumberFields.QuadraticField.RingOfIntegers
import QuadraticNumberFields.RingOfIntegers.Discriminant
import QuadraticNumberFields.Splitting.Factorization
import QuadraticNumberFields.Splitting.Qsqrtd.Monogenic

/-!
# Minkowski Bounds for Quadratic Class Groups

This file specializes mathlib's Minkowski ideal-class representative bound to
the standard quadratic fields `Qsqrtd d`.

Source alignment: the Minkowski constants follow Boxer Notes, Lectures 23.1
and 23.2.
-/

open scoped NumberField Real nonZeroDivisors QuadraticNumberFields.ClassGroup

open Module NumberField InfinitePlace Ideal Nat
open Qsqrtd

/-! ## General class-group generation from prime divisors -/

namespace ClassGroup

section General

variable {R : Type*} [CommRing R] [IsDedekindDomain R]

/-- If every nonzero prime ideal divisor of a nonzero ideal has class in a subgroup
of the class group, then the ideal's class also lies in that subgroup. -/
theorem mk0_mem_subgroup_of_forall_prime_dvd_mem
    (H : Subgroup (ClassGroup R)) (I : Ideal R) (hI0 : I ≠ 0)
    (h : ∀ P : (Ideal R)⁰, (P : Ideal R).IsPrime → (P : Ideal R) ∣ I →
      mk0 P ∈ H) :
    mk0 ⟨I, mem_nonZeroDivisors_iff_ne_zero.mpr hI0⟩ ∈ H := by
  induction I using UniqueFactorizationMonoid.induction_on_prime with
  | h₁ =>
      exact (hI0 rfl).elim
  | h₂ J hJ =>
      have hJtop : J = ⊤ := Ideal.isUnit_iff.mp hJ
      subst J
      have hmk : mk0 ⟨(⊤ : Ideal R), mem_nonZeroDivisors_iff_ne_zero.mpr hI0⟩ = 1 := by
        rw [mk0_eq_one_iff]
        exact ⟨1, Ideal.span_singleton_one.symm⟩
      rw [hmk]
      exact H.one_mem
  | h₃ J P _hJ hP ih =>
      have hP0 : P ≠ 0 := hP.ne_zero
      have hJ0 : J ≠ 0 := right_ne_zero_of_mul hI0
      have hPmem : mk0 ⟨P, mem_nonZeroDivisors_iff_ne_zero.mpr hP0⟩ ∈ H :=
        h ⟨P, mem_nonZeroDivisors_iff_ne_zero.mpr hP0⟩
          (Ideal.isPrime_of_prime hP) (dvd_mul_right P J)
      have hJmem : mk0 ⟨J, mem_nonZeroDivisors_iff_ne_zero.mpr hJ0⟩ ∈ H :=
        ih hJ0 fun Q hQ hQdvd => h Q hQ (hQdvd.mul_left P)
      have hmul := H.mul_mem hPmem hJmem
      rw [← map_mul (mk0 : (Ideal R)⁰ →* ClassGroup R)] at hmul
      simpa using hmul

end General

end ClassGroup

/-! ## Quadratic Minkowski bounds -/

namespace QuadraticNumberFields

-- Use the canonical `QuadraticAlgebra` algebra structure for standard `Qsqrtd`
-- calculations. Explicit bridges below still use `DivisionRing.toRatAlgebra`
-- when matching mathlib's generic number-field API.
attribute [-instance] DivisionRing.toRatAlgebra

-- Same definition in 'Mathlib.NumberTheory.NumberField.ClassNumber'
local notation "N " K:70 => @finrank ℚ K _ _ (@Algebra.toModule ℚ K _ _ DivisionRing.toRatAlgebra)
local notation "M " K:70 => (4 / π) ^ nrComplexPlaces K *
  (((N K)! : ℝ) / (N K) ^ (N K) * √|discr K|)

namespace Qsqrtd

section QuadraticMinkowski

private theorem minkowskiConstant_eq_imaginary
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] (hd : d < 0) :
    M (Qsqrtd (d : ℚ)) = (2 / π) * √ |(discr (Qsqrtd (d : ℚ)) : ℝ)| := by
  rw [nrComplexPlaces_eq_one_of_neg d hd]
  rw [finrank_ratAlgebra_eq_two]
  ring

private theorem minkowskiConstant_eq_real
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] (hd : 0 < d) :
    M (Qsqrtd (d : ℚ)) = (1 / 2) * √ |(discr (Qsqrtd (d : ℚ)) : ℝ)| := by
  rw [nrComplexPlaces_eq_zero_of_pos d hd]
  rw [finrank_ratAlgebra_eq_two]
  norm_num

/-- In an imaginary quadratic field `ℚ(√d)`, every ideal class has a representative
whose norm is at most `(2 / π) * √|D_K|`. -/
theorem exists_ideal_in_class_of_norm_le_imaginary
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] (hd : d < 0)
    (C : ClassGroup (𝓞 (Qsqrtd (d : ℚ)))) :
    ∃ I : nonZeroDivisors (Ideal (𝓞 (Qsqrtd (d : ℚ)))),
      ClassGroup.mk0 I = C ∧
        (absNorm (I : Ideal (𝓞 (Qsqrtd (d : ℚ)))) : ℝ) ≤
          (2 / π) * √ |(discr (Qsqrtd (d : ℚ)) : ℝ)| := by
  obtain ⟨I, hC, hI⟩ := NumberField.exists_ideal_in_class_of_norm_le C
  refine ⟨I, hC, ?_⟩
  convert hI using 1
  exact (minkowskiConstant_eq_imaginary d hd).symm

/-- In a real quadratic field `ℚ(√d)`, every ideal class has a representative whose
norm is at most `(1 / 2) * √|D_K|`. -/
theorem exists_ideal_in_class_of_norm_le_real
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] (hd : 0 < d)
    (C : ClassGroup (𝓞 (Qsqrtd (d : ℚ)))) :
    ∃ I : nonZeroDivisors (Ideal (𝓞 (Qsqrtd (d : ℚ)))),
      ClassGroup.mk0 I = C ∧
        (absNorm (I : Ideal (𝓞 (Qsqrtd (d : ℚ)))) : ℝ) ≤
          (1 / 2) * √ |(discr (Qsqrtd (d : ℚ)) : ℝ)| := by
  obtain ⟨I, hC, hI⟩ := NumberField.exists_ideal_in_class_of_norm_le C
  refine ⟨I, hC, ?_⟩
  convert hI using 1
  exact (minkowskiConstant_eq_real d hd).symm

/-- The **Minkowski class-representative bound** of the quadratic field `ℚ(√d)`,
a first-class real invariant alongside `discr`. It specializes the general
number-field bound `(4/π)^{r₂} · (n!/nⁿ) · √|D|` to degree `2`
(`n!/nⁿ = 2/4 = 1/2`):

* imaginary `d < 0`: `(2/π)·√|D|`;
* real `d > 0`: `(1/2)·√|D|`. -/
noncomputable def minkowskiBound (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] : ℝ :=
  (4 / π) ^ nrComplexPlaces (Qsqrtd (d : ℚ)) * (1 / 2) *
    √ |(discr (Qsqrtd (d : ℚ)) : ℝ)|

/-- Minkowski's bound for `ℚ(√d)` (unified form): every ideal class has a
representative whose absolute norm is at most `minkowskiBound d`. -/
theorem exists_ideal_in_class_of_norm_le
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)]
    (C : ClassGroup (𝓞 (Qsqrtd (d : ℚ)))) :
    ∃ I : nonZeroDivisors (Ideal (𝓞 (Qsqrtd (d : ℚ)))),
      ClassGroup.mk0 I = C ∧
        (absNorm (I : Ideal (𝓞 (Qsqrtd (d : ℚ)))) : ℝ) ≤ minkowskiBound d := by
  rcases lt_trichotomy d 0 with hneg | h0 | hpos
  · obtain ⟨I, hC, hI⟩ := exists_ideal_in_class_of_norm_le_imaginary d hneg C
    refine ⟨I, hC, ?_⟩
    rw [minkowskiBound, nrComplexPlaces_eq_one_of_neg d hneg]
    ring_nf at hI ⊢
    exact hI
  · exact absurd h0 (Fact.out : Squarefree d).ne_zero
  · obtain ⟨I, hC, hI⟩ := exists_ideal_in_class_of_norm_le_real d hpos C
    refine ⟨I, hC, ?_⟩
    rw [minkowskiBound, nrComplexPlaces_eq_zero_of_pos d hpos]
    ring_nf at hI ⊢
    exact hI

/-! ## Generation by prime ideals below the Minkowski bound -/

/-- Every ideal class of `𝓞(ℚ(√d))` lies in the subgroup generated by classes of
nonzero prime ideals whose absolute norm is at most `minkowskiBound d`. -/
theorem classGroup_mem_closure_prime_ideals_le_minkowskiBound
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] (C : Cl(d)) :
    C ∈ Subgroup.closure
      {C' : Cl(d) |
        ∃ P : (Ideal (𝓞 (Qsqrtd (d : ℚ))))⁰,
          (P : Ideal (𝓞 (Qsqrtd (d : ℚ)))).IsPrime ∧
          (Ideal.absNorm (P : Ideal (𝓞 (Qsqrtd (d : ℚ)))) : ℝ) ≤ minkowskiBound d ∧
          ClassGroup.mk0 P = C'} := by
  let H : Subgroup Cl(d) := Subgroup.closure
    {C' : Cl(d) |
      ∃ P : (Ideal (𝓞 (Qsqrtd (d : ℚ))))⁰,
        (P : Ideal (𝓞 (Qsqrtd (d : ℚ)))).IsPrime ∧
        (Ideal.absNorm (P : Ideal (𝓞 (Qsqrtd (d : ℚ)))) : ℝ) ≤ minkowskiBound d ∧
        ClassGroup.mk0 P = C'}
  obtain ⟨I, hmk, hnorm⟩ := exists_ideal_in_class_of_norm_le d C
  rw [← hmk]
  refine ClassGroup.mk0_mem_subgroup_of_forall_prime_dvd_mem H
    (I : Ideal (𝓞 (Qsqrtd (d : ℚ)))) (nonZeroDivisors.coe_ne_zero I) ?_
  intro P hP hPI
  refine Subgroup.subset_closure ?_
  refine ⟨P, hP, ?_, rfl⟩
  have hIabs0 : Ideal.absNorm (I : Ideal (𝓞 (Qsqrtd (d : ℚ)))) ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff]
    exact nonZeroDivisors.coe_ne_zero I
  have hPle :
      Ideal.absNorm (P : Ideal (𝓞 (Qsqrtd (d : ℚ)))) ≤
        Ideal.absNorm (I : Ideal (𝓞 (Qsqrtd (d : ℚ)))) :=
    Nat.le_of_dvd (Nat.pos_of_ne_zero hIabs0)
      (Ideal.absNorm_dvd_absNorm_of_le (Ideal.le_of_dvd hPI))
  exact le_trans (by exact_mod_cast hPle) hnorm

/-- The ideal class group `Cl(𝓞(ℚ(√d)))` is generated by the classes of nonzero
prime ideals whose absolute norm is at most `minkowskiBound d`. -/
theorem classGroup_closure_prime_ideals_le_minkowskiBound_eq_top
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] :
    Subgroup.closure
      {C : Cl(d) |
        ∃ P : (Ideal (𝓞 (Qsqrtd (d : ℚ))))⁰,
          (P : Ideal (𝓞 (Qsqrtd (d : ℚ)))).IsPrime ∧
          (Ideal.absNorm (P : Ideal (𝓞 (Qsqrtd (d : ℚ)))) : ℝ) ≤ minkowskiBound d ∧
          ClassGroup.mk0 P = C} =
      ⊤ := by
  rw [eq_top_iff]
  intro C _hC
  exact classGroup_mem_closure_prime_ideals_le_minkowskiBound d C

/-! ## Class number one via prime ideals below the Minkowski bound -/

section ClassNumberOne

open scoped QuadraticNumberFields.Splitting

/-- Numeric estimate for the Minkowski bound of an imaginary quadratic field:
if `4 · |D| < 9 · n²` then `(2/π) · √|D| < n`. The factor `9` lets the proof
run on the crude estimate `π > 3`, which is sharp enough for all nine Heegner
numbers. -/
theorem minkowskiBound_lt_of_neg (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)]
    (hd : d < 0) {n : ℕ}
    (hn : 4 * |NumberField.discr (Qsqrtd (d : ℚ))| < 9 * (n : ℤ) ^ 2) :
    minkowskiBound d < n := by
  set D : ℤ := NumberField.discr (Qsqrtd (d : ℚ)) with hD
  have hn0 : (0 : ℝ) < n := by
    have habs : 0 ≤ |D| := abs_nonneg D
    have : 0 < n := by by_contra h0; interval_cases n; simp at hn; omega
    exact_mod_cast this
  rw [minkowskiBound, nrComplexPlaces_eq_one_of_neg d hd, pow_one, ← hD]
  have hpi : (3 : ℝ) < π := Real.pi_gt_three
  have h9 : 4 * |(D : ℝ)| < 9 * (n : ℝ) ^ 2 := by
    rw [← Int.cast_abs]
    exact_mod_cast hn
  have hsq : √|(D : ℝ)| < 3 * n / 2 := by
    refine (Real.sqrt_lt' (by linarith)).mpr ?_
    nlinarith
  rw [div_mul_eq_mul_div, div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
  nlinarith [Real.sqrt_nonneg |(D : ℝ)|]

private lemma exists_nat_prime_comap_eq_p_and_dvd_absNorm
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)]
    {P : Ideal (𝓞 (Qsqrtd (d : ℚ)))}
    (hP : P.IsPrime) (hP0 : P ≠ ⊥) :
    ∃ p : ℕ, p.Prime ∧
      Ideal.comap (algebraMap ℤ (𝓞 (Qsqrtd (d : ℚ)))) P = 𝔭(p) ∧
        p ∣ Ideal.absNorm P := by
  exact Ideal.exists_nat_prime_comap_eq_span_and_dvd_absNorm_of_isPrime hP hP0

private lemma isPrincipal_of_isInertIn_of_comap_eq_p
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)]
    {P : Ideal (𝓞 (Qsqrtd (d : ℚ)))}
    (hP : P.IsPrime) {p : ℕ} (hp : p.Prime)
    (hcomap : Ideal.comap (algebraMap ℤ (𝓞 (Qsqrtd (d : ℚ)))) P = 𝔭(p))
    (hinert : Ideal.IsInertIn (𝔭(p)) 𝓞(d)) :
    P.IsPrincipal := by
  have hchar : ringChar ℤ ≠ 2 := by simp [ringChar.eq_zero]
  have hpbot : (𝔭(p)) ≠ (⊥ : Ideal ℤ) := by
    rw [Ne, Ideal.span_singleton_eq_bot, Nat.cast_eq_zero]
    exact hp.ne_zero
  haveI : (𝔭(p)).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible
      ((Nat.prime_iff_prime_int.mp hp).irreducible)
  have hQprime : (Ideal.map (algebraMap ℤ (𝓞 (Qsqrtd (d : ℚ)))) (𝔭(p))).IsPrime :=
    Ideal.map_isPrime_of_isInertIn (𝔭(p)) (𝓞 (Qsqrtd (d : ℚ))) hchar hpbot hinert
  have hQle : Ideal.map (algebraMap ℤ (𝓞 (Qsqrtd (d : ℚ)))) (𝔭(p)) ≤ P := by
    rw [← hcomap]
    exact Ideal.map_comap_le
  have hQbot : Ideal.map (algebraMap ℤ (𝓞 (Qsqrtd (d : ℚ)))) (𝔭(p)) ≠ ⊥ := by
    rw [Ideal.map_span, Set.image_singleton, Ne, Ideal.span_singleton_eq_bot]
    simp only [map_natCast, Nat.cast_eq_zero]
    exact hp.ne_zero
  have hPQ : Ideal.map (algebraMap ℤ (𝓞 (Qsqrtd (d : ℚ)))) (𝔭(p)) = P :=
    (hQprime.isMaximal hQbot).eq_of_le hP.ne_top hQle
  rw [← hPQ, Ideal.map_span, Set.image_singleton]
  exact ⟨_, rfl⟩

/-- Class-group form of the Minkowski-bound prime-ideal principality criterion:
if every nonzero prime ideal with absolute norm at most `minkowskiBound d` is
principal, then every ideal class of `𝓞(ℚ(√d))` is trivial. -/
theorem classGroup_eq_one_of_forall_le_minkowskiBound_isPrincipal
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)]
    (h : ∀ P : Ideal (𝓞 (Qsqrtd (d : ℚ))), P.IsPrime → P ≠ ⊥ →
      (Ideal.absNorm P : ℝ) ≤ minkowskiBound d → P.IsPrincipal)
    (C : ClassGroup (𝓞 (Qsqrtd (d : ℚ)))) :
    C = 1 := by
  obtain ⟨I, hmk, hnorm⟩ := exists_ideal_in_class_of_norm_le d C
  rw [← hmk, ClassGroup.mk0_eq_one_iff]
  refine Ideal.isPrincipal_of_forall_isPrime_dvd_isPrincipal fun P hP hPI => ?_
  have hI0 : (I : Ideal (𝓞 (Qsqrtd (d : ℚ)))) ≠ 0 := nonZeroDivisors.coe_ne_zero I
  have hP0 : P ≠ ⊥ := by
    rintro rfl
    rw [← Ideal.zero_eq_bot, zero_dvd_iff] at hPI
    exact hI0 hPI
  have hIabs0 : Ideal.absNorm (I : Ideal (𝓞 (Qsqrtd (d : ℚ)))) ≠ 0 := by
    rwa [Ne, Ideal.absNorm_eq_zero_iff]
  have hPle : Ideal.absNorm P ≤ Ideal.absNorm (I : Ideal (𝓞 (Qsqrtd (d : ℚ)))) :=
    Nat.le_of_dvd (Nat.pos_of_ne_zero hIabs0)
      (Ideal.absNorm_dvd_absNorm_of_le (Ideal.le_of_dvd hPI))
  have hPbound : (Ideal.absNorm P : ℝ) ≤ minkowskiBound d :=
    le_trans (by exact_mod_cast hPle) hnorm
  exact h P hP hP0 hPbound

/-- Class number one from bounded prime ideals. If every nonzero prime ideal
of `𝓞(ℚ(√d))` with absolute norm at most `minkowskiBound d` is principal, then
`ℚ(√d)` has class number one. -/
theorem classNumber_eq_one_of_forall_le_minkowskiBound_isPrincipal
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)]
    (h : ∀ P : Ideal (𝓞 (Qsqrtd (d : ℚ))), P.IsPrime → P ≠ ⊥ →
      (Ideal.absNorm P : ℝ) ≤ minkowskiBound d → P.IsPrincipal) :
    NumberField.classNumber (Qsqrtd (d : ℚ)) = 1 := by
  exact NumberField.classNumber_eq_one_of_forall_classGroup_eq_one
    (classGroup_eq_one_of_forall_le_minkowskiBound_isPrincipal d h)

/-- Class-group form of the rational-prime fiber criterion: if for every rational
prime `p ≤ minkowskiBound d` all prime ideals above `(p)` are principal, then
every ideal class of `𝓞(ℚ(√d))` is trivial. -/
theorem classGroup_eq_one_of_forall_le_minkowskiBound_primesOver_isPrincipal
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)]
    (h : ∀ p : ℕ, p.Prime → (p : ℝ) ≤ minkowskiBound d →
      ∀ P ∈ Ideal.primesOver (𝔭(p)) 𝓞(d), P.IsPrincipal)
    (C : ClassGroup (𝓞 (Qsqrtd (d : ℚ)))) :
    C = 1 := by
  refine classGroup_eq_one_of_forall_le_minkowskiBound_isPrincipal d ?_ C
  intro P hP hP0 hPbound
  obtain ⟨p, hp, hcomap, hpdiv⟩ :=
    exists_nat_prime_comap_eq_p_and_dvd_absNorm d hP hP0
  have habs0 : Ideal.absNorm P ≠ 0 := by
    rwa [Ne, Ideal.absNorm_eq_zero_iff]
  have hpabs : p ≤ Ideal.absNorm P :=
    Nat.le_of_dvd (Nat.pos_of_ne_zero habs0) hpdiv
  have hple : (p : ℝ) ≤ minkowskiBound d :=
    le_trans (by exact_mod_cast hpabs) hPbound
  letI : P.LiesOver (𝔭(p)) := ⟨hcomap.symm⟩
  exact h p hp hple P ⟨hP, inferInstance⟩

/-- **Class number one from principal rational-prime fibers.** If every prime
ideal above every rational prime `p ≤ minkowskiBound d` is principal, then
`ℚ(√d)` has class number one. -/
theorem classNumber_eq_one_of_forall_le_minkowskiBound_primesOver_isPrincipal
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)]
    (h : ∀ p : ℕ, p.Prime → (p : ℝ) ≤ minkowskiBound d →
      ∀ P ∈ Ideal.primesOver (𝔭(p)) 𝓞(d), P.IsPrincipal) :
    NumberField.classNumber (Qsqrtd (d : ℚ)) = 1 := by
  exact NumberField.classNumber_eq_one_of_forall_classGroup_eq_one
    (classGroup_eq_one_of_forall_le_minkowskiBound_primesOver_isPrincipal d h)

/-- **Class number one via inert or split small primes.** Inert primes contribute
only the principal ideal `(p)`; for split primes, it is enough to prove
principality of every prime ideal above `(p)`. -/
theorem classNumber_eq_one_of_forall_le_minkowskiBound_split_principal
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)]
    (hinert_or_split : ∀ p : ℕ, p.Prime → (p : ℝ) ≤ minkowskiBound d →
      Ideal.IsInertIn (𝔭(p)) 𝓞(d) ∨ Ideal.IsSplitIn (𝔭(p)) 𝓞(d))
    (hsplit : ∀ p : ℕ, p.Prime → (p : ℝ) ≤ minkowskiBound d →
      Ideal.IsSplitIn (𝔭(p)) 𝓞(d) →
        ∀ P ∈ Ideal.primesOver (𝔭(p)) 𝓞(d), P.IsPrincipal) :
    NumberField.classNumber (Qsqrtd (d : ℚ)) = 1 := by
  refine classNumber_eq_one_of_forall_le_minkowskiBound_primesOver_isPrincipal d ?_
  intro p hp hple P hPmem
  rcases hinert_or_split p hp hple with hinert | hsplitp
  · letI : P.LiesOver (𝔭(p)) := hPmem.2
    exact isPrincipal_of_isInertIn_of_comap_eq_p d hPmem.1 hp
      (Ideal.LiesOver.over (p := 𝔭(p)) (P := P)).symm hinert
  · exact hsplit p hp hple hsplitp P hPmem

/-- **Class number one via inert or ramified small primes.** Inert primes
contribute only the principal ideal `(p)`; for ramified primes, it is enough to
prove principality of every prime ideal above `(p)`. -/
theorem classNumber_eq_one_of_forall_le_minkowskiBound_ramified_principal
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)]
    (hinert_or_ramified : ∀ p : ℕ, p.Prime → (p : ℝ) ≤ minkowskiBound d →
      Ideal.IsInertIn (𝔭(p)) 𝓞(d) ∨ Ideal.IsRamifiedIn (𝔭(p)) 𝓞(d))
    (hramified : ∀ p : ℕ, p.Prime → (p : ℝ) ≤ minkowskiBound d →
      Ideal.IsRamifiedIn (𝔭(p)) 𝓞(d) →
        ∀ P ∈ Ideal.primesOver (𝔭(p)) 𝓞(d), P.IsPrincipal) :
    NumberField.classNumber (Qsqrtd (d : ℚ)) = 1 := by
  refine classNumber_eq_one_of_forall_le_minkowskiBound_primesOver_isPrincipal d ?_
  intro p hp hple P hPmem
  rcases hinert_or_ramified p hp hple with hinert | hramifiedp
  · letI : P.LiesOver (𝔭(p)) := hPmem.2
    exact isPrincipal_of_isInertIn_of_comap_eq_p d hPmem.1 hp
      (Ideal.LiesOver.over (p := 𝔭(p)) (P := P)).symm hinert
  · exact hramified p hp hple hramifiedp P hPmem

/-- Class-group form of the inert-prime criterion: under the Minkowski-bound
inertness hypothesis, every ideal class of `𝓞(ℚ(√d))` is trivial. -/
theorem classGroup_eq_one_of_forall_le_minkowskiBound_isInertIn
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)]
    (h : ∀ p : ℕ, p.Prime → (p : ℝ) ≤ minkowskiBound d →
      Ideal.IsInertIn (𝔭(p)) 𝓞(d))
    (C : ClassGroup (𝓞 (Qsqrtd (d : ℚ)))) :
    C = 1 := by
  refine classGroup_eq_one_of_forall_le_minkowskiBound_primesOver_isPrincipal d ?_ C
  intro p hp hple P hPmem
  letI : P.LiesOver (𝔭(p)) := hPmem.2
  exact isPrincipal_of_isInertIn_of_comap_eq_p d hPmem.1 hp
    (Ideal.LiesOver.over (p := 𝔭(p)) (P := P)).symm (h p hp hple)

/-- **Class number one via inert primes.** If every rational prime `p` below
the Minkowski bound of `ℚ(√d)` is inert in `𝓞(ℚ(√d))`, then `ℚ(√d)` has class
number one.

Every ideal class contains an ideal `I` with `absNorm I ≤ minkowskiBound d`.
Each prime ideal `P ∣ I` lies over a rational prime `p ≤ absNorm P ≤ absNorm I`,
which is inert by hypothesis, so `P = (p)` is principal; hence `I` is principal
and the class group is trivial. -/
theorem classNumber_eq_one_of_forall_le_minkowskiBound_isInertIn
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)]
    (h : ∀ p : ℕ, p.Prime → (p : ℝ) ≤ minkowskiBound d →
      Ideal.IsInertIn (𝔭(p)) 𝓞(d)) :
    NumberField.classNumber (Qsqrtd (d : ℚ)) = 1 := by
  exact NumberField.classNumber_eq_one_of_forall_classGroup_eq_one
    (classGroup_eq_one_of_forall_le_minkowskiBound_isInertIn d h)

end ClassNumberOne

end QuadraticMinkowski

end Qsqrtd
end QuadraticNumberFields
