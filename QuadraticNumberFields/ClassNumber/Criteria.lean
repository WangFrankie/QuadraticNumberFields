/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/

import QNFMathlib.RingTheory.DedekindDomain.Ideal
import QNFMathlib.RingTheory.Ideal.Norm.AbsNorm
import QuadraticNumberFields.ClassNumber.Minkowski
import QuadraticNumberFields.Splitting.Factorization
import QuadraticNumberFields.Splitting.Qsqrtd.Monogenic

/-!
# Class-Number-One Criteria from Minkowski Bounds

This file proves class-number-one criteria for `Qsqrtd d` from the Minkowski
representative bound and splitting behavior of small rational primes.
-/

open scoped NumberField Real
open scoped QuadraticNumberFields.Splitting

open Module NumberField InfinitePlace Ideal Nat

namespace QuadraticNumberFields

attribute [-instance] DivisionRing.toRatAlgebra

namespace Qsqrtd

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

private lemma isPrincipal_of_isPrime_dvd_of_forall_le_minkowskiBound_isInertIn
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)]
    (h : ∀ p : ℕ, p.Prime → (p : ℝ) ≤ minkowskiBound d →
      Ideal.IsInertIn (𝔭(p)) 𝓞(d))
    {I : nonZeroDivisors (Ideal (𝓞 (Qsqrtd (d : ℚ))))}
    {P : Ideal (𝓞 (Qsqrtd (d : ℚ)))}
    (hP : P.IsPrime) (hPI : P ∣ (I : Ideal (𝓞 (Qsqrtd (d : ℚ)))))
    (hnorm : (Ideal.absNorm (I : Ideal (𝓞 (Qsqrtd (d : ℚ)))) : ℝ) ≤
      minkowskiBound d) :
    P.IsPrincipal := by
  have hI0 : (I : Ideal (𝓞 (Qsqrtd (d : ℚ)))) ≠ 0 := nonZeroDivisors.coe_ne_zero I
  have hP0 : P ≠ ⊥ := by
    rintro rfl
    rw [← Ideal.zero_eq_bot, zero_dvd_iff] at hPI
    exact hI0 hPI
  obtain ⟨p, hp, hcomap, hpdiv⟩ :=
    exists_nat_prime_comap_eq_p_and_dvd_absNorm d hP hP0
  have habs0 : Ideal.absNorm P ≠ 0 := by
    rwa [Ne, Ideal.absNorm_eq_zero_iff]
  have hIabs0 : Ideal.absNorm (I : Ideal (𝓞 (Qsqrtd (d : ℚ)))) ≠ 0 := by
    rwa [Ne, Ideal.absNorm_eq_zero_iff]
  have hPle : Ideal.absNorm P ≤ Ideal.absNorm (I : Ideal (𝓞 (Qsqrtd (d : ℚ)))) :=
    Nat.le_of_dvd (Nat.pos_of_ne_zero hIabs0)
      (Ideal.absNorm_dvd_absNorm_of_le (Ideal.le_of_dvd hPI))
  have hpabs : p ≤ Ideal.absNorm P :=
    Nat.le_of_dvd (Nat.pos_of_ne_zero habs0) hpdiv
  have hple : (p : ℝ) ≤ minkowskiBound d :=
    le_trans (by exact_mod_cast le_trans hpabs hPle) hnorm
  exact isPrincipal_of_isInertIn_of_comap_eq_p d hP hp hcomap (h p hp hple)

private lemma isPrincipal_of_isPrime_dvd_of_forall_le_minkowskiBound_primesOver_isPrincipal
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)]
    (h : ∀ p : ℕ, p.Prime → (p : ℝ) ≤ minkowskiBound d →
      ∀ P ∈ Ideal.primesOver (𝔭(p)) 𝓞(d), P.IsPrincipal)
    {I : nonZeroDivisors (Ideal (𝓞 (Qsqrtd (d : ℚ))))}
    {P : Ideal (𝓞 (Qsqrtd (d : ℚ)))}
    (hP : P.IsPrime) (hPI : P ∣ (I : Ideal (𝓞 (Qsqrtd (d : ℚ)))))
    (hnorm : (Ideal.absNorm (I : Ideal (𝓞 (Qsqrtd (d : ℚ)))) : ℝ) ≤
      minkowskiBound d) :
    P.IsPrincipal := by
  have hI0 : (I : Ideal (𝓞 (Qsqrtd (d : ℚ)))) ≠ 0 := nonZeroDivisors.coe_ne_zero I
  have hP0 : P ≠ ⊥ := by
    rintro rfl
    rw [← Ideal.zero_eq_bot, zero_dvd_iff] at hPI
    exact hI0 hPI
  obtain ⟨p, hp, hcomap, hpdiv⟩ :=
    exists_nat_prime_comap_eq_p_and_dvd_absNorm d hP hP0
  have habs0 : Ideal.absNorm P ≠ 0 := by
    rwa [Ne, Ideal.absNorm_eq_zero_iff]
  have hIabs0 : Ideal.absNorm (I : Ideal (𝓞 (Qsqrtd (d : ℚ)))) ≠ 0 := by
    rwa [Ne, Ideal.absNorm_eq_zero_iff]
  have hPle : Ideal.absNorm P ≤ Ideal.absNorm (I : Ideal (𝓞 (Qsqrtd (d : ℚ)))) :=
    Nat.le_of_dvd (Nat.pos_of_ne_zero hIabs0)
      (Ideal.absNorm_dvd_absNorm_of_le (Ideal.le_of_dvd hPI))
  have hpabs : p ≤ Ideal.absNorm P :=
    Nat.le_of_dvd (Nat.pos_of_ne_zero habs0) hpdiv
  have hple : (p : ℝ) ≤ minkowskiBound d :=
    le_trans (by exact_mod_cast le_trans hpabs hPle) hnorm
  have hlies : P.LiesOver (𝔭(p)) := by
    exact ⟨by simpa [Ideal.under] using hcomap.symm⟩
  have hmem : P ∈ Ideal.primesOver (𝔭(p)) 𝓞(d) := ⟨hP, hlies⟩
  exact h p hp hple P hmem

private lemma isPrincipal_of_absNorm_le_minkowskiBound_of_forall_isInertIn
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)]
    (h : ∀ p : ℕ, p.Prime → (p : ℝ) ≤ minkowskiBound d →
      Ideal.IsInertIn (𝔭(p)) 𝓞(d))
    (I : nonZeroDivisors (Ideal (𝓞 (Qsqrtd (d : ℚ)))))
    (hnorm : (Ideal.absNorm (I : Ideal (𝓞 (Qsqrtd (d : ℚ)))) : ℝ) ≤
      minkowskiBound d) :
    (I : Ideal (𝓞 (Qsqrtd (d : ℚ)))).IsPrincipal := by
  refine Ideal.isPrincipal_of_forall_isPrime_dvd_isPrincipal fun P hP hPI => ?_
  exact isPrincipal_of_isPrime_dvd_of_forall_le_minkowskiBound_isInertIn
    d h hP hPI hnorm

private lemma isPrincipal_of_absNorm_le_minkowskiBound_of_forall_primesOver_isPrincipal
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)]
    (h : ∀ p : ℕ, p.Prime → (p : ℝ) ≤ minkowskiBound d →
      ∀ P ∈ Ideal.primesOver (𝔭(p)) 𝓞(d), P.IsPrincipal)
    (I : nonZeroDivisors (Ideal (𝓞 (Qsqrtd (d : ℚ)))))
    (hnorm : (Ideal.absNorm (I : Ideal (𝓞 (Qsqrtd (d : ℚ)))) : ℝ) ≤
      minkowskiBound d) :
    (I : Ideal (𝓞 (Qsqrtd (d : ℚ)))).IsPrincipal := by
  refine Ideal.isPrincipal_of_forall_isPrime_dvd_isPrincipal fun P hP hPI => ?_
  exact isPrincipal_of_isPrime_dvd_of_forall_le_minkowskiBound_primesOver_isPrincipal
    d h hP hPI hnorm

/-- Class-group form of the inert-prime criterion: under the Minkowski-bound
inertness hypothesis, every ideal class of `𝓞(ℚ(√d))` is trivial. -/
theorem classGroup_eq_one_of_forall_le_minkowskiBound_isInertIn
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)]
    (h : ∀ p : ℕ, p.Prime → (p : ℝ) ≤ minkowskiBound d →
      Ideal.IsInertIn (𝔭(p)) 𝓞(d))
    (C : ClassGroup (𝓞 (Qsqrtd (d : ℚ)))) :
    C = 1 := by
  obtain ⟨I, hmk, hnorm⟩ := exists_ideal_in_class_of_norm_le d C
  rw [← hmk, ClassGroup.mk0_eq_one_iff]
  exact isPrincipal_of_absNorm_le_minkowskiBound_of_forall_isInertIn d h I hnorm

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
  have htriv := classGroup_eq_one_of_forall_le_minkowskiBound_isInertIn d h
  haveI : Unique (ClassGroup (𝓞 (Qsqrtd (d : ℚ)))) := ⟨⟨1⟩, htriv⟩
  simpa only [NumberField.classNumber] using
    Fintype.card_unique (α := ClassGroup (𝓞 (Qsqrtd (d : ℚ))))

/-- Class number one via Minkowski and principal small-prime fibres.  If every
prime ideal above every rational prime below the Minkowski bound is principal,
then every ideal class has a principal representative. -/
theorem classNumber_eq_one_of_forall_le_minkowskiBound_primesOver_isPrincipal
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)]
    (h : ∀ p : ℕ, p.Prime → (p : ℝ) ≤ minkowskiBound d →
      ∀ P ∈ Ideal.primesOver (𝔭(p)) 𝓞(d), P.IsPrincipal) :
    NumberField.classNumber (Qsqrtd (d : ℚ)) = 1 := by
  have htriv : ∀ C : ClassGroup (𝓞 (Qsqrtd (d : ℚ))), C = 1 := by
    intro C
    obtain ⟨I, hmk, hnorm⟩ := exists_ideal_in_class_of_norm_le d C
    rw [← hmk, ClassGroup.mk0_eq_one_iff]
    exact isPrincipal_of_absNorm_le_minkowskiBound_of_forall_primesOver_isPrincipal
      d h I hnorm
  exact NumberField.classNumber_eq_one_of_forall_classGroup_eq_one htriv

/-- Class number one when every small rational prime is inert or split, and the
prime ideals above the split small primes are principal. -/
theorem classNumber_eq_one_of_forall_le_minkowskiBound_split_principal
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)]
    (hinert_or_split : ∀ p : ℕ, p.Prime → (p : ℝ) ≤ minkowskiBound d →
      Ideal.IsInertIn (𝔭(p)) 𝓞(d) ∨ Ideal.IsSplitIn (𝔭(p)) 𝓞(d))
    (hsplit : ∀ p : ℕ, p.Prime → (p : ℝ) ≤ minkowskiBound d →
      Ideal.IsSplitIn (𝔭(p)) 𝓞(d) →
      ∀ P ∈ Ideal.primesOver (𝔭(p)) 𝓞(d), P.IsPrincipal) :
    NumberField.classNumber (Qsqrtd (d : ℚ)) = 1 := by
  refine classNumber_eq_one_of_forall_le_minkowskiBound_primesOver_isPrincipal d
    fun p hp hple P hPmem => ?_
  rcases hinert_or_split p hp hple with hinert | hsplit_p
  · exact isPrincipal_of_isInertIn_of_comap_eq_p d hPmem.1 hp
      (by simpa [Ideal.under] using hPmem.2.over.symm) hinert
  · exact hsplit p hp hple hsplit_p P hPmem

/-- Class number one when every small rational prime is inert or ramified, and the
prime ideals above the ramified small primes are principal. -/
theorem classNumber_eq_one_of_forall_le_minkowskiBound_ramified_principal
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)]
    (hinert_or_ramified : ∀ p : ℕ, p.Prime → (p : ℝ) ≤ minkowskiBound d →
      Ideal.IsInertIn (𝔭(p)) 𝓞(d) ∨ Ideal.IsRamifiedIn (𝔭(p)) 𝓞(d))
    (hramified : ∀ p : ℕ, p.Prime → (p : ℝ) ≤ minkowskiBound d →
      Ideal.IsRamifiedIn (𝔭(p)) 𝓞(d) →
      ∀ P ∈ Ideal.primesOver (𝔭(p)) 𝓞(d), P.IsPrincipal) :
    NumberField.classNumber (Qsqrtd (d : ℚ)) = 1 := by
  refine classNumber_eq_one_of_forall_le_minkowskiBound_primesOver_isPrincipal d
    fun p hp hple P hPmem => ?_
  rcases hinert_or_ramified p hp hple with hinert | hramified_p
  · exact isPrincipal_of_isInertIn_of_comap_eq_p d hPmem.1 hp
      (by simpa [Ideal.under] using hPmem.2.over.symm) hinert
  · exact hramified p hp hple hramified_p P hPmem

end Qsqrtd
end QuadraticNumberFields
