/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/

import QuadraticNumberFields.ClassGroup.GenusTheory.AmbiguousIdeals.Representatives
import QuadraticNumberFields.ClassGroup.SmallNorm

/-!
# Positive-Principal Ramified Parity: Internal Foundations

Shared internal infrastructure for the positive-principal genus-theory input:
norm and `absNorm` computations on explicit `√d` generators, ramified-prime
ideal facts, square detection on ambiguous-ideal norms, and the factorization of
an ambiguous ideal into the full ramified-parity ideal product. These results are
consumed by the ordinary-principal, imaginary, and real branches and live in the
`GenusTheory.Internal` namespace.
-/

namespace QuadraticNumberFields
namespace ClassGroup
namespace GenusTheory

open scoped nonZeroDivisors NumberField Pointwise QuadraticNumberFields.ClassGroup
open scoped QuadraticNumberFields.Splitting

attribute [-instance] DivisionRing.toRatAlgebra
attribute [local instance] FractionRing.liftAlgebra

namespace Internal

theorem exists_toPrincipalIdeal_eq_mk0_of_isPrincipal
    {R : Type*} [CommRing R] [IsDomain R] [IsDedekindDomain R]
    {I : (Ideal R)⁰} (hI : (I : Ideal R).IsPrincipal) :
    ∃ γ : (FractionRing R)ˣ,
      toPrincipalIdeal R (FractionRing R) γ = FractionalIdeal.mk0 (FractionRing R) I := by
  classical
  letI : (I : Ideal R).IsPrincipal := hI
  let a : R := Submodule.IsPrincipal.generator (I : Ideal R)
  have hIa : Ideal.span ({a} : Set R) = (I : Ideal R) := by
    simp [a]
  have hI0 : (I : Ideal R) ≠ ⊥ := by
    exact mem_nonZeroDivisors_iff_ne_zero.mp I.2
  have ha0 : a ≠ 0 := by
    intro ha
    apply hI0
    rw [← hIa, ha, Ideal.span_singleton_eq_bot]
  let γ : (FractionRing R)ˣ := Units.mk0 (algebraMap R (FractionRing R) a) (by
    simpa using (FaithfulSMul.algebraMap_injective R (FractionRing R)).ne ha0)
  refine ⟨γ, ?_⟩
  rw [toPrincipalIdeal_eq_iff]
  change FractionalIdeal.spanSingleton R⁰ (algebraMap R (FractionRing R) a) =
    (FractionalIdeal.mk0 (FractionRing R) I : FractionalIdeal R⁰ (FractionRing R))
  rw [← FractionalIdeal.coeIdeal_span_singleton (P := FractionRing R) a, hIa]
  rfl

private theorem algebraNorm_sqrtdInt
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] :
    Algebra.norm ℤ (Splitting.sqrtdInt d) = -d := by
  apply Int.cast_injective (α := ℚ)
  rw [Algebra.coe_norm_int (K := Qsqrtd (d : ℚ)),
    Qsqrtd.algebraNorm_ratAlgebra_eq_qsqrtdNorm]
  rw [Splitting.coe_sqrtdInt]
  simp [Qsqrtd.norm, QuadraticAlgebra.norm, QuadraticAlgebra.omega]

private theorem absNorm_span_sqrtdInt
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] :
    Ideal.absNorm
        (Ideal.span
          ({Splitting.sqrtdInt d} :
            Set (NumberField.RingOfIntegers (Qsqrtd (d : ℚ))))) =
      d.natAbs := by
  rw [Ideal.absNorm_span_singleton, algebraNorm_sqrtdInt]
  simp

private theorem algebraNorm_intCast_add_sqrtdInt
    (d a : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] :
    Algebra.norm ℤ
        (algebraMap ℤ (NumberField.RingOfIntegers (Qsqrtd (d : ℚ))) a +
          Splitting.sqrtdInt d) =
      a ^ 2 - d := by
  apply Int.cast_injective (α := ℚ)
  rw [Algebra.coe_norm_int (K := Qsqrtd (d : ℚ)),
    Qsqrtd.algebraNorm_ratAlgebra_eq_qsqrtdNorm]
  have hcoord :
      ((algebraMap ℤ (NumberField.RingOfIntegers (Qsqrtd (d : ℚ))) a +
            Splitting.sqrtdInt d :
          NumberField.RingOfIntegers (Qsqrtd (d : ℚ))) :
        Qsqrtd (d : ℚ)) =
        (⟨(a : ℚ), 1⟩ : Qsqrtd (d : ℚ)) := by
    ext <;> simp [Splitting.coe_sqrtdInt, QuadraticAlgebra.omega]
  rw [hcoord]
  change QuadraticAlgebra.norm (⟨(a : ℚ), 1⟩ : Qsqrtd (d : ℚ)) =
    ((a ^ 2 - d : ℤ) : ℚ)
  simp [QuadraticAlgebra.norm_mk]
  ring

theorem qsqrt_norm_fractionRing_intCast_add_sqrtdInt
    (d a : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] :
    let R := NumberField.RingOfIntegers (Qsqrtd (d : ℚ))
    (Qsqrtd.norm
      (FractionRing.algEquiv R (Qsqrtd (d : ℚ))
        (algebraMap R (FractionRing R)
          (algebraMap ℤ R a + Splitting.sqrtdInt d))) : ℝ) =
      ((a ^ 2 - d : ℤ) : ℝ) := by
  intro R
  have hmap :
      FractionRing.algEquiv R (Qsqrtd (d : ℚ))
          (algebraMap R (FractionRing R)
            (algebraMap ℤ R a + Splitting.sqrtdInt d)) =
        ((algebraMap ℤ R a + Splitting.sqrtdInt d : R) : Qsqrtd (d : ℚ)) := by
    simp [R]
  rw [hmap]
  have hcoord :
      ((algebraMap ℤ R a + Splitting.sqrtdInt d : R) : Qsqrtd (d : ℚ)) =
        (⟨(a : ℚ), 1⟩ : Qsqrtd (d : ℚ)) := by
    ext <;> simp [R, Splitting.coe_sqrtdInt, QuadraticAlgebra.omega]
  rw [hcoord]
  change ((QuadraticAlgebra.norm (⟨(a : ℚ), 1⟩ : Qsqrtd (d : ℚ)) : ℚ) : ℝ) =
    ((a ^ 2 - d : ℤ) : ℝ)
  simp [QuadraticAlgebra.norm_mk]
  ring

theorem intCast_add_sqrtdInt_ne_zero_of_lt_sq
    (d a : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] (hda : d < a ^ 2) :
    algebraMap ℤ (NumberField.RingOfIntegers (Qsqrtd (d : ℚ))) a +
      Splitting.sqrtdInt d ≠ 0 := by
  intro hzero
  have hnorm_zero :
      Algebra.norm ℤ
          (algebraMap ℤ (NumberField.RingOfIntegers (Qsqrtd (d : ℚ))) a +
            Splitting.sqrtdInt d) = 0 := by
    rw [hzero]
    simp
  rw [algebraNorm_intCast_add_sqrtdInt d a] at hnorm_zero
  omega

theorem qsqrt_norm_fractionRing_intCast_add_sqrtdInt_pos
    (d a : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] (hda : d < a ^ 2) :
    let R := NumberField.RingOfIntegers (Qsqrtd (d : ℚ))
    0 <
      (Qsqrtd.norm
        (FractionRing.algEquiv R (Qsqrtd (d : ℚ))
          (algebraMap R (FractionRing R)
            (algebraMap ℤ R a + Splitting.sqrtdInt d))) : ℝ) := by
  intro R
  rw [qsqrt_norm_fractionRing_intCast_add_sqrtdInt d a]
  exact_mod_cast (sub_pos.mpr hda)

theorem exists_positive_norm_generator_of_span_intCast_add_sqrtdInt_eq
    (d a : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)]
    {r : {p // p ∈ ramifiedPrimes d} → Fin 2} (hda : d < a ^ 2)
    (hrnonzero : ∃ p, r p ≠ 0)
    (hspan :
      Ideal.span
          ({algebraMap ℤ (NumberField.RingOfIntegers (Qsqrtd (d : ℚ))) a +
              Splitting.sqrtdInt d} :
            Set (NumberField.RingOfIntegers (Qsqrtd (d : ℚ)))) =
        (fullRamifiedParityIdealProduct d r :
          Ideal (NumberField.RingOfIntegers (Qsqrtd (d : ℚ))))) :
    let R := NumberField.RingOfIntegers (Qsqrtd (d : ℚ))
    ∃ r : ({p // p ∈ ramifiedPrimes d} → Fin 2),
      (∃ p, r p ≠ 0) ∧
        ∃ γ : (FractionRing R)ˣ,
          toPrincipalIdeal R (FractionRing R) γ =
              FractionalIdeal.mk0 (FractionRing R) (fullRamifiedParityIdealProduct d r) ∧
            0 <
              (Qsqrtd.norm
                (FractionRing.algEquiv R (Qsqrtd (d : ℚ)) (γ : FractionRing R)) : ℝ) := by
  classical
  intro R
  let α : R := algebraMap ℤ R a + Splitting.sqrtdInt d
  have hα0 : α ≠ 0 := by
    simpa [α, R] using intCast_add_sqrtdInt_ne_zero_of_lt_sq d a hda
  let γ : (FractionRing R)ˣ :=
    Units.mk0 (algebraMap R (FractionRing R) α) (by
      simpa using (FaithfulSMul.algebraMap_injective R (FractionRing R)).ne hα0)
  refine ⟨r, hrnonzero, γ, ?_, ?_⟩
  · rw [toPrincipalIdeal_eq_iff]
    change FractionalIdeal.spanSingleton R⁰ (algebraMap R (FractionRing R) α) =
      (FractionalIdeal.mk0 (FractionRing R) (fullRamifiedParityIdealProduct d r) :
        FractionalIdeal R⁰ (FractionRing R))
    rw [← FractionalIdeal.coeIdeal_span_singleton (P := FractionRing R) α]
    rw [hspan]
    rfl
  · simpa [γ, α, R] using qsqrt_norm_fractionRing_intCast_add_sqrtdInt_pos d a hda

private theorem algebraNorm_one_add_sqrtdInt
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] :
    Algebra.norm ℤ
        ((1 + Splitting.sqrtdInt d) : NumberField.RingOfIntegers (Qsqrtd (d : ℚ))) =
      1 - d := by
  simpa using algebraNorm_intCast_add_sqrtdInt d 1

private theorem absNorm_span_one_add_sqrtdInt_neg_one :
    Ideal.absNorm
        (Ideal.span
          ({(1 + Splitting.sqrtdInt (-1))} :
            Set (NumberField.RingOfIntegers (Qsqrtd ((-1 : ℤ) : ℚ))))) =
      2 := by
  rw [Ideal.absNorm_span_singleton, algebraNorm_one_add_sqrtdInt]
  norm_num

private theorem one_add_sqrtdInt_mul_one_sub_sqrtdInt_neg_one :
    ((1 + Splitting.sqrtdInt (-1)) * (1 - Splitting.sqrtdInt (-1)) :
      NumberField.RingOfIntegers (Qsqrtd ((-1 : ℤ) : ℚ))) = 2 := by
  let K := Qsqrtd ((-1 : ℤ) : ℚ)
  let R := NumberField.RingOfIntegers K
  apply NumberField.RingOfIntegers.ext
  change (((1 + Splitting.sqrtdInt (-1) : R) : K) *
      ((1 - Splitting.sqrtdInt (-1) : R) : K)) = (2 : K)
  have hleft : ((1 + Splitting.sqrtdInt (-1) : R) : K) = (⟨1, 1⟩ : K) := by
    rw [NumberField.RingOfIntegers.coe_eq_algebraMap, map_add, map_one,
      ← NumberField.RingOfIntegers.coe_eq_algebraMap (Splitting.sqrtdInt (-1)),
      Splitting.coe_sqrtdInt]
    ext
    · change (1 : ℚ) + 0 = 1
      norm_num
    · change (0 : ℚ) + 1 = 1
      norm_num
  have hright : ((1 - Splitting.sqrtdInt (-1) : R) : K) = (⟨1, -1⟩ : K) := by
    rw [NumberField.RingOfIntegers.coe_eq_algebraMap, map_sub, map_one,
      ← NumberField.RingOfIntegers.coe_eq_algebraMap (Splitting.sqrtdInt (-1)),
      Splitting.coe_sqrtdInt]
    ext
    · change (1 : ℚ) - 0 = 1
      norm_num
    · change (0 : ℚ) - 1 = -1
      norm_num
  rw [hleft, hright]
  change ((⟨1, 1⟩ : K) * (⟨1, -1⟩ : K)) = (⟨2, 0⟩ : K)
  ext
  · change (1 : ℚ) * 1 + ((-1 : ℤ) : ℚ) * 1 * (-1) = 2
    norm_num
  · change (1 : ℚ) * (-1) + 1 * 1 + (0 : ℚ) * 1 * (-1) = 0
    norm_num

private theorem span_one_add_sqrtdInt_neg_one_mem_primesOver_two :
    Ideal.span
        ({(1 + Splitting.sqrtdInt (-1))} :
          Set (NumberField.RingOfIntegers (Qsqrtd ((-1 : ℤ) : ℚ)))) ∈
      Ideal.primesOver (𝔭(2))
        (NumberField.RingOfIntegers (Qsqrtd ((-1 : ℤ) : ℚ))) := by
  let R := NumberField.RingOfIntegers (Qsqrtd ((-1 : ℤ) : ℚ))
  let I : Ideal R := Ideal.span ({(1 + Splitting.sqrtdInt (-1))} : Set R)
  have hIprime : I.IsPrime := by
    exact Ideal.isPrime_of_absNorm_eq_two
      (by simpa [I] using absNorm_span_one_add_sqrtdInt_neg_one)
  refine ⟨hIprime, ?_⟩
  have h2mem : (2 : R) ∈ I := by
    change (2 : R) ∈ Ideal.span ({(1 + Splitting.sqrtdInt (-1))} : Set R)
    rw [Ideal.mem_span_singleton]
    refine ⟨(1 - Splitting.sqrtdInt (-1) : R), ?_⟩
    exact one_add_sqrtdInt_mul_one_sub_sqrtdInt_neg_one.symm
  have hle : (𝔭(2) : Ideal ℤ) ≤ I.comap (algebraMap ℤ R) := by
    rw [Ideal.span_singleton_le_iff_mem]
    exact h2mem
  have hmax : (𝔭(2) : Ideal ℤ).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible
      ((Nat.prime_iff_prime_int.mp Nat.prime_two).irreducible)
  have hne : I.comap (algebraMap ℤ R) ≠ ⊤ :=
    Ideal.comap_ne_top (algebraMap ℤ R) hIprime.ne_top
  exact ⟨hmax.eq_of_le hne hle⟩

theorem two_mem_ramifiedPrimes_neg_one : 2 ∈ ramifiedPrimes (-1) := by
  exact (mem_ramifiedPrimes_iff_isRamifiedIn (-1) 2).mpr
    ⟨Nat.prime_two, Splitting.isRamified_two_of_mod_four_ne_one (-1) (by decide)⟩

theorem ramifiedPrimeIdeal_two_neg_one_isPrincipal :
    (ramifiedPrimeIdeal (-1) two_mem_ramifiedPrimes_neg_one :
      Ideal (NumberField.RingOfIntegers (Qsqrtd ((-1 : ℤ) : ℚ)))).IsPrincipal := by
  let R := NumberField.RingOfIntegers (Qsqrtd ((-1 : ℤ) : ℚ))
  let I : Ideal R := Ideal.span ({(1 + Splitting.sqrtdInt (-1))} : Set R)
  have hI_mem : I ∈ Ideal.primesOver (𝔭(2)) R := by
    simpa [I, R] using span_one_add_sqrtdInt_neg_one_mem_primesOver_two
  have hIeq : I = ramifiedPrimeIdeal (-1) two_mem_ramifiedPrimes_neg_one := by
    have hsingleton :=
      primesOver_eq_singleton_ramifiedPrimeIdeal (-1) two_mem_ramifiedPrimes_neg_one
    have hmem_single :
        I ∈ ({ramifiedPrimeIdeal (-1) two_mem_ramifiedPrimes_neg_one} : Set (Ideal R)) := by
      have hsingletonR :
          Ideal.primesOver (𝔭(2)) R =
            {ramifiedPrimeIdeal (-1) two_mem_ramifiedPrimes_neg_one} := by
        simpa [R] using hsingleton
      simpa [hsingletonR] using hI_mem
    simpa using hmem_single
  rw [← hIeq]
  change (Ideal.span ({(1 + Splitting.sqrtdInt (-1))} : Set R)).IsPrincipal
  exact ⟨1 + Splitting.sqrtdInt (-1), rfl⟩

private theorem pow_dvd_multiset_prod_of_le_count
    {M : Type*} [CommMonoid M] [DecidableEq M]
    (s : Multiset M) (a : M) {n : ℕ} (h : n ≤ s.count a) :
    a ^ n ∣ s.prod := by
  have hrep : Multiset.replicate n a ≤ s :=
    (Multiset.le_count_iff_replicate_le).mp h
  have hdiv := Multiset.prod_dvd_prod_of_le hrep
  simpa [Multiset.prod_replicate] using hdiv

private theorem absNorm_span_nat_prime (p : ℕ) :
    Ideal.absNorm (𝔭(p) : Ideal ℤ) = p := by
  rw [Ideal.absNorm_span_singleton]
  change (Algebra.norm ℤ (p : ℤ)).natAbs = p
  simp

private theorem nat_prime_dvd_absNorm_ramifiedPrimeIdeal
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)]
    {p : ℕ} (hp : p ∈ ramifiedPrimes d) :
    p ∣ Ideal.absNorm (ramifiedPrimeIdeal d hp) := by
  have hdiv :
      Ideal.absNorm ((ramifiedPrimeIdeal d hp).under ℤ) ∣
        Ideal.absNorm (ramifiedPrimeIdeal d hp) :=
    Int.absNorm_under_dvd_absNorm (ramifiedPrimeIdeal d hp)
  have hunder : (ramifiedPrimeIdeal d hp).under ℤ = 𝔭(p) :=
    (ramifiedPrimeIdeal_mem_primesOver d hp).2.1.symm
  rw [hunder, absNorm_span_nat_prime p] at hdiv
  exact hdiv

theorem fullRamifiedParityVector_ramifiedPrimeIdeal_self_ne_zero
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)]
    {p : ℕ} (hp : p ∈ ramifiedPrimes d) :
    fullRamifiedParityVector d
      ⟨ramifiedPrimeIdeal d hp,
        mem_nonZeroDivisors_iff_ne_zero.mpr (ramifiedPrimeIdeal_ne_bot d hp)⟩
        ⟨p, hp⟩ ≠ 0 := by
  let P : Ideal (NumberField.RingOfIntegers (Qsqrtd (d : ℚ))) := ramifiedPrimeIdeal d hp
  have hPmem : P ∈ Ideal.primesOver (𝔭(p))
      (NumberField.RingOfIntegers (Qsqrtd (d : ℚ))) := by
    simpa [P] using ramifiedPrimeIdeal_mem_primesOver d hp
  have hPprime : P.IsPrime := hPmem.1
  have hP0 : P ≠ ⊥ := by
    simpa [P] using ramifiedPrimeIdeal_ne_bot d hp
  have hPprimeElem : Prime P := (Ideal.prime_iff_isPrime hP0).mpr hPprime
  have hPirr : Irreducible P := hPprimeElem.irreducible
  have hnf : UniqueFactorizationMonoid.normalizedFactors P = {P} := by
    rw [UniqueFactorizationMonoid.normalizedFactors_irreducible hPirr]
    simp [P]
  change (⟨(UniqueFactorizationMonoid.normalizedFactors P).count P % 2,
    Nat.mod_lt _ (by decide : 0 < 2)⟩ : Fin 2) ≠ 0
  rw [hnf]
  norm_num

private theorem absNorm_sq_dvd_of_two_le_normalizedFactors_count
    {R : Type*} [CommRing R] [Nontrivial R] [IsDedekindDomain R] [Module.Free ℤ R]
    {I P : Ideal R} (hI : I ≠ ⊥)
    (hcount : 2 ≤ (UniqueFactorizationMonoid.normalizedFactors I).count P) :
    Ideal.absNorm P ^ 2 ∣ Ideal.absNorm I := by
  have hP2_dvd : P ^ 2 ∣ I := by
    have h := pow_dvd_multiset_prod_of_le_count
      (UniqueFactorizationMonoid.normalizedFactors I) P hcount
    rwa [Ideal.prod_normalizedFactors_eq_self hI] at h
  have hnorm := map_dvd Ideal.absNorm hP2_dvd
  simpa using hnorm

private theorem not_absNorm_sq_dvd_squarefree_natAbs
    {d : ℤ} (hsq : Squarefree d) {p n : ℕ} (hp : p.Prime) (hpn : p ∣ n) :
    ¬ n ^ 2 ∣ d.natAbs := by
  intro hn2
  have hsq_nat : Squarefree d.natAbs := Int.squarefree_natAbs.mpr hsq
  have hp2_dvd_n2 : p ^ 2 ∣ n ^ 2 := by
    simpa [pow_two] using mul_dvd_mul hpn hpn
  have hp2_dvd_d : p ^ 2 ∣ d.natAbs := dvd_trans hp2_dvd_n2 hn2
  have hno := (Nat.squarefree_iff_prime_squarefree.mp hsq_nat) p hp
  exact hno (by simpa [pow_two] using hp2_dvd_d)

private theorem two_le_count_of_fullRamifiedParityVector_eq_zero_of_mem
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)]
    (J : (Ideal (NumberField.RingOfIntegers (Qsqrtd (d : ℚ))))⁰)
    (p : {p // p ∈ ramifiedPrimes d})
    (hparity : fullRamifiedParityVector d J p = 0)
    (hmem : ramifiedPrimeIdeal d p.2 ∈
      UniqueFactorizationMonoid.normalizedFactors
        (J : Ideal (NumberField.RingOfIntegers (Qsqrtd (d : ℚ))))) :
    2 ≤ (UniqueFactorizationMonoid.normalizedFactors
      (J : Ideal (NumberField.RingOfIntegers (Qsqrtd (d : ℚ))))).count
        (ramifiedPrimeIdeal d p.2) := by
  let s := UniqueFactorizationMonoid.normalizedFactors
    (J : Ideal (NumberField.RingOfIntegers (Qsqrtd (d : ℚ))))
  let n := s.count (ramifiedPrimeIdeal d p.2)
  have hpos : 0 < n := by
    simpa [n, s] using (Multiset.count_pos.mpr hmem)
  have hmod : n % 2 = 0 := by
    have hval := congrArg Fin.val hparity
    simpa [fullRamifiedParityVector, n, s] using hval
  have h2dvd : 2 ∣ n := Nat.dvd_of_mod_eq_zero hmod
  change 2 ≤ n
  obtain ⟨k, hk⟩ := h2dvd
  rw [hk] at hpos ⊢
  rcases k with _ | k
  · simp at hpos
  · omega

private theorem two_dvd_count_ramifiedPrimeIdeal_of_fullRamifiedParityVector_eq_zero
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)]
    (J : (Ideal (NumberField.RingOfIntegers (Qsqrtd (d : ℚ))))⁰)
    (p : {p // p ∈ ramifiedPrimes d})
    (hparity : fullRamifiedParityVector d J p = 0) :
    2 ∣ (UniqueFactorizationMonoid.normalizedFactors
      (J : Ideal (NumberField.RingOfIntegers (Qsqrtd (d : ℚ))))).count
        (ramifiedPrimeIdeal d p.2) := by
  let s := UniqueFactorizationMonoid.normalizedFactors
    (J : Ideal (NumberField.RingOfIntegers (Qsqrtd (d : ℚ))))
  let n := s.count (ramifiedPrimeIdeal d p.2)
  have hmod : n % 2 = 0 := by
    have hval := congrArg Fin.val hparity
    simpa [fullRamifiedParityVector, n, s] using hval
  exact Nat.dvd_of_mod_eq_zero hmod

private theorem isSquare_pow_of_two_dvd_nat (a n : ℕ) (hn : 2 ∣ n) :
    IsSquare (a ^ n) := by
  obtain ⟨k, rfl⟩ := hn
  exact Even.isSquare_pow ⟨k, by rw [two_mul]⟩ a

private theorem isSquare_finset_prod_of_involution
    {α M : Type*} [CommMonoid M]
    (s : Finset α) (f : α → M) (σ : α → α)
    (hσmem : ∀ a ∈ s, σ a ∈ s)
    (hσinv : ∀ a ∈ s, σ (σ a) = a)
    (hfixed : ∀ a ∈ s, σ a = a → IsSquare (f a))
    (hpair : ∀ a ∈ s, σ a ≠ a → f (σ a) = f a) :
    IsSquare (∏ a ∈ s, f a) := by
  classical
  have hmain :
      ∀ n, ∀ t : Finset α, t.card = n →
        (∀ a ∈ t, σ a ∈ t) →
        (∀ a ∈ t, σ (σ a) = a) →
        (∀ a ∈ t, σ a = a → IsSquare (f a)) →
        (∀ a ∈ t, σ a ≠ a → f (σ a) = f a) →
        IsSquare (∏ a ∈ t, f a) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
        intro t htcard hσmem hσinv hfixed hpair
        by_cases ht_empty : t = ∅
        · simp [ht_empty]
        · have ht_nonempty : t.Nonempty := Finset.nonempty_iff_ne_empty.mpr ht_empty
          obtain ⟨a, ha⟩ := ht_nonempty
          by_cases hσa : σ a = a
          · let u := t.erase a
            have hcard_u : u.card < n := by
              rw [← htcard]
              exact Finset.card_erase_lt_of_mem ha
            have ih' : IsSquare (∏ b ∈ u, f b) := by
              refine ih u.card hcard_u u rfl ?_ ?_ ?_ ?_
              · intro b hb
                rw [Finset.mem_erase] at hb
                have hσb_mem_t : σ b ∈ t := hσmem b hb.2
                have hσb_ne_a : σ b ≠ a := by
                  intro hσb
                  have hb_eq_a : b = a := by
                    calc
                      b = σ (σ b) := (hσinv b hb.2).symm
                      _ = σ a := by rw [hσb]
                      _ = a := hσa
                  exact hb.1 hb_eq_a
                exact Finset.mem_erase.mpr ⟨hσb_ne_a, hσb_mem_t⟩
              · intro b hb
                rw [Finset.mem_erase] at hb
                exact hσinv b hb.2
              · intro b hb hbfix
                rw [Finset.mem_erase] at hb
                exact hfixed b hb.2 hbfix
              · intro b hb hbne
                rw [Finset.mem_erase] at hb
                exact hpair b hb.2 hbne
            rw [← Finset.mul_prod_erase t f ha]
            exact (hfixed a ha hσa).mul ih'
          · have hσa_mem_t : σ a ∈ t := hσmem a ha
            have hσa_mem_erase_a : σ a ∈ t.erase a :=
              Finset.mem_erase.mpr ⟨hσa, hσa_mem_t⟩
            let u := (t.erase a).erase (σ a)
            have hcard_u : u.card < n := by
              have h₁ : u.card < (t.erase a).card := by
                exact Finset.card_erase_lt_of_mem hσa_mem_erase_a
              have h₂ : (t.erase a).card < n := by
                rw [← htcard]
                exact Finset.card_erase_lt_of_mem ha
              exact lt_trans h₁ h₂
            have ih' : IsSquare (∏ b ∈ u, f b) := by
              refine ih u.card hcard_u u rfl ?_ ?_ ?_ ?_
              · intro b hb
                rw [Finset.mem_erase] at hb
                rw [Finset.mem_erase] at hb
                have hb_ne_σa : b ≠ σ a := hb.1
                have hb_ne_a : b ≠ a := hb.2.1
                have hb_t : b ∈ t := hb.2.2
                have hσb_mem_t : σ b ∈ t := hσmem b hb_t
                have hσb_ne_a : σ b ≠ a := by
                  intro hσb
                  have hb_eq_σa : b = σ a := by
                    calc
                      b = σ (σ b) := (hσinv b hb_t).symm
                      _ = σ a := by rw [hσb]
                  exact hb_ne_σa hb_eq_σa
                have hσb_ne_σa : σ b ≠ σ a := by
                  intro hσb
                  have hb_eq_a : b = a := by
                    calc
                      b = σ (σ b) := (hσinv b hb_t).symm
                      _ = σ (σ a) := by rw [hσb]
                      _ = a := hσinv a ha
                  exact hb_ne_a hb_eq_a
                exact Finset.mem_erase.mpr
                  ⟨hσb_ne_σa, Finset.mem_erase.mpr ⟨hσb_ne_a, hσb_mem_t⟩⟩
              · intro b hb
                rw [Finset.mem_erase] at hb
                rw [Finset.mem_erase] at hb
                exact hσinv b hb.2.2
              · intro b hb hbfix
                rw [Finset.mem_erase] at hb
                rw [Finset.mem_erase] at hb
                exact hfixed b hb.2.2 hbfix
              · intro b hb hbne
                rw [Finset.mem_erase] at hb
                rw [Finset.mem_erase] at hb
                exact hpair b hb.2.2 hbne
            have hpair_sq : IsSquare (f a * f (σ a)) := by
              rw [hpair a ha hσa]
              exact IsSquare.mul_self (f a)
            rw [← Finset.mul_prod_erase t f ha]
            rw [← Finset.mul_prod_erase (t.erase a) f hσa_mem_erase_a]
            simpa [mul_assoc] using hpair_sq.mul ih'
  exact hmain s.card s rfl hσmem hσinv hfixed hpair

private theorem exists_normalizedFactor_mem_primesOver_of_nat_prime_dvd_absNorm
    {R : Type*} [CommRing R] [Nontrivial R] [Algebra ℤ R] [IsDedekindDomain R]
    [Module.Free ℤ R] [Module.Finite ℤ R]
    {I : Ideal R} (hI0 : I ≠ ⊥) {p : ℕ} (hp : p.Prime)
    (hpdiv : p ∣ Ideal.absNorm I) :
    ∃ P : Ideal R,
      P ∈ UniqueFactorizationMonoid.normalizedFactors I ∧
        P ∈ Ideal.primesOver (𝔭(p)) R := by
  letI : Fact p.Prime := ⟨hp⟩
  have hnot_sup : I ⊔ Ideal.span ({(p : R)} : Set R) ≠ ⊤ := by
    intro htop
    have hcop : (Ideal.absNorm I).Coprime p :=
      Ideal.absNorm_coprime_prime_of_sup_span_natCast_eq_top I p hI0 htop
    have hcop' : p.Coprime (Ideal.absNorm I) := Nat.coprime_comm.mp hcop
    exact ((Nat.Prime.coprime_iff_not_dvd hp).mp hcop') hpdiv
  obtain ⟨M, hMmax, hsupM⟩ := Ideal.exists_le_maximal
    (I ⊔ Ideal.span ({(p : R)} : Set R)) hnot_sup
  have hIle : I ≤ M := le_sup_left.trans hsupM
  have hpSpan_le : Ideal.span ({(p : R)} : Set R) ≤ M := le_sup_right.trans hsupM
  have hmap : Ideal.map (algebraMap ℤ R) (𝔭(p)) = Ideal.span ({(p : R)} : Set R) := by
    rw [Ideal.map_span, Set.image_singleton]
    simp
  have hlecomap : (𝔭(p) : Ideal ℤ) ≤ M.comap (algebraMap ℤ R) := by
    rw [← Ideal.map_le_iff_le_comap, hmap]
    exact hpSpan_le
  have hcomap_ne_top : M.comap (algebraMap ℤ R) ≠ ⊤ := by
    intro htop
    apply hMmax.ne_top
    rw [Ideal.eq_top_iff_one]
    have hone : (1 : ℤ) ∈ M.comap (algebraMap ℤ R) := by
      rw [htop]
      trivial
    simpa using hone
  haveI : (𝔭(p) : Ideal ℤ).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible
      ((Nat.prime_iff_prime_int.mp hp).irreducible)
  have hcomap : M.comap (algebraMap ℤ R) = 𝔭(p) := by
    exact (show (𝔭(p) : Ideal ℤ) = M.comap (algebraMap ℤ R) from
      (show (𝔭(p) : Ideal ℤ).IsMaximal from inferInstance).eq_of_le
        hcomap_ne_top hlecomap).symm
  refine ⟨M, ?_, ?_⟩
  · exact (Ideal.mem_normalizedFactors_iff hI0).mpr ⟨hMmax.isPrime, hIle⟩
  · exact ⟨hMmax.isPrime, ⟨hcomap.symm⟩⟩

private theorem absNorm_eq_prime_pow_inertiaDeg_of_comap_eq_p
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)]
    {P : Ideal (NumberField.RingOfIntegers (Qsqrtd (d : ℚ)))}
    {p : ℕ} (hp : p.Prime)
    (hcomap :
      P.comap (algebraMap ℤ (NumberField.RingOfIntegers (Qsqrtd (d : ℚ)))) = 𝔭(p)) :
    Ideal.absNorm P = p ^ ((𝔭(p)).inertiaDeg P) := by
  let R := NumberField.RingOfIntegers (Qsqrtd (d : ℚ))
  letI : P.LiesOver (𝔭(p)) := ⟨hcomap.symm⟩
  simpa [R] using (Ideal.absNorm_eq_pow_inertiaDeg' (P := P) hp)

private theorem absNorm_eq_prime_of_isSplitIn_of_comap_eq_p
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)]
    {P : Ideal (NumberField.RingOfIntegers (Qsqrtd (d : ℚ)))}
    (hPprime : P.IsPrime) {p : ℕ} (hp : p.Prime)
    (hcomap :
      P.comap (algebraMap ℤ (NumberField.RingOfIntegers (Qsqrtd (d : ℚ)))) = 𝔭(p))
    (hsplit : Ideal.IsSplitIn (𝔭(p))
      (NumberField.RingOfIntegers (Qsqrtd (d : ℚ)))) :
    Ideal.absNorm P = p := by
  let R := NumberField.RingOfIntegers (Qsqrtd (d : ℚ))
  have hpbot : (𝔭(p)) ≠ (⊥ : Ideal ℤ) := by
    rw [Ne, Ideal.span_singleton_eq_bot, Nat.cast_eq_zero]
    exact hp.ne_zero
  haveI : (𝔭(p)).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible
      ((Nat.prime_iff_prime_int.mp hp).irreducible)
  letI : P.IsPrime := hPprime
  letI : P.LiesOver (𝔭(p)) := ⟨hcomap.symm⟩
  rw [absNorm_eq_prime_pow_inertiaDeg_of_comap_eq_p d hp hcomap,
    Ideal.inertiaDeg_eq_one_of_isSplitIn (p := 𝔭(p)) (S := R)
      (by norm_num : ringChar ℤ ≠ 2) hsplit,
    pow_one]

private theorem absNorm_eq_prime_sq_of_isInertIn_of_comap_eq_p
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)]
    {P : Ideal (NumberField.RingOfIntegers (Qsqrtd (d : ℚ)))}
    (hPprime : P.IsPrime) {p : ℕ} (hp : p.Prime)
    (hcomap :
      P.comap (algebraMap ℤ (NumberField.RingOfIntegers (Qsqrtd (d : ℚ)))) = 𝔭(p))
    (hinert : Ideal.IsInertIn (𝔭(p))
      (NumberField.RingOfIntegers (Qsqrtd (d : ℚ)))) :
    Ideal.absNorm P = p ^ 2 := by
  let R := NumberField.RingOfIntegers (Qsqrtd (d : ℚ))
  have hpbot : (𝔭(p)) ≠ (⊥ : Ideal ℤ) := by
    rw [Ne, Ideal.span_singleton_eq_bot, Nat.cast_eq_zero]
    exact hp.ne_zero
  haveI : (𝔭(p)).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible
      ((Nat.prime_iff_prime_int.mp hp).irreducible)
  letI : P.IsPrime := hPprime
  letI : P.LiesOver (𝔭(p)) := ⟨hcomap.symm⟩
  rw [absNorm_eq_prime_pow_inertiaDeg_of_comap_eq_p d hp hcomap,
    Ideal.inertiaDeg_eq_two_of_isInertIn (p := 𝔭(p)) (S := R)
      (by norm_num : ringChar ℤ ≠ 2) hpbot hinert]

private theorem absNorm_eq_prime_of_isRamifiedIn_of_comap_eq_p
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)]
    {P : Ideal (NumberField.RingOfIntegers (Qsqrtd (d : ℚ)))}
    (hPprime : P.IsPrime) {p : ℕ} (hp : p.Prime)
    (hcomap :
      P.comap (algebraMap ℤ (NumberField.RingOfIntegers (Qsqrtd (d : ℚ)))) = 𝔭(p))
    (hram : Ideal.IsRamifiedIn (𝔭(p))
      (NumberField.RingOfIntegers (Qsqrtd (d : ℚ)))) :
    Ideal.absNorm P = p := by
  let R := NumberField.RingOfIntegers (Qsqrtd (d : ℚ))
  have hpbot : (𝔭(p)) ≠ (⊥ : Ideal ℤ) := by
    rw [Ne, Ideal.span_singleton_eq_bot, Nat.cast_eq_zero]
    exact hp.ne_zero
  haveI : (𝔭(p)).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible
      ((Nat.prime_iff_prime_int.mp hp).irreducible)
  letI : P.IsPrime := hPprime
  letI : P.LiesOver (𝔭(p)) := ⟨hcomap.symm⟩
  rw [absNorm_eq_prime_pow_inertiaDeg_of_comap_eq_p d hp hcomap,
    Ideal.inertiaDeg_eq_one_of_isRamifiedIn (p := 𝔭(p)) (S := R)
      (by norm_num : ringChar ℤ ≠ 2) hpbot hram,
    pow_one]

private theorem normalizedFactors_ramified_absNorm_count_prod_eq_prime_count_prod
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)]
    (J : (Ideal (NumberField.RingOfIntegers (Qsqrtd (d : ℚ))))⁰)
    [DecidablePred (fun P :
        {P // P ∈ UniqueFactorizationMonoid.normalizedFactors
          (J : Ideal (NumberField.RingOfIntegers (Qsqrtd (d : ℚ))))} =>
      normalizedFactorIsRamified d P)] :
    (∏ P ∈
        (UniqueFactorizationMonoid.normalizedFactors
          (J : Ideal (NumberField.RingOfIntegers (Qsqrtd (d : ℚ))))).attach.toFinset with
        normalizedFactorIsRamified d P,
      Ideal.absNorm P.1 ^
        (UniqueFactorizationMonoid.normalizedFactors
          (J : Ideal (NumberField.RingOfIntegers (Qsqrtd (d : ℚ))))).count P.1) =
      Finset.univ.prod fun p : {p // p ∈ ramifiedPrimes d} =>
        p.1 ^
          (UniqueFactorizationMonoid.normalizedFactors
            (J : Ideal (NumberField.RingOfIntegers (Qsqrtd (d : ℚ))))).count
            (ramifiedPrimeIdeal d p.2) := by
  classical
  let R := NumberField.RingOfIntegers (Qsqrtd (d : ℚ))
  let s := UniqueFactorizationMonoid.normalizedFactors (J : Ideal R)
  let S := s.attach.toFinset
  let f : {P // P ∈ s} → ℕ := fun P => Ideal.absNorm P.1 ^ s.count P.1
  let term : {p // p ∈ ramifiedPrimes d} → ℕ := fun p =>
    p.1 ^ s.count (ramifiedPrimeIdeal d p.2)
  let T := Finset.univ.filter fun p : {p // p ∈ ramifiedPrimes d} =>
    ramifiedPrimeIdeal d p.2 ∈ s
  have hleft :
      (∏ P ∈ S with normalizedFactorIsRamified d P, f P) = ∏ p ∈ T, term p := by
    refine Finset.prod_bij
      (fun P hP => ramifiedPrimeOfNormalizedFactor d P (Finset.mem_filter.mp hP).2)
      ?_ ?_ ?_ ?_
    · intro P hP
      rw [Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ?_⟩
      have hPram : normalizedFactorIsRamified d P := (Finset.mem_filter.mp hP).2
      have hP_eq :=
        normalizedFactor_eq_ramifiedPrimeIdeal_ramifiedPrimeOfNormalizedFactor d P hPram
      rw [← hP_eq]
      exact P.2
    · intro P hP Q hQ hpq
      apply Subtype.ext
      have hP_eq :=
        normalizedFactor_eq_ramifiedPrimeIdeal_ramifiedPrimeOfNormalizedFactor d P
          (Finset.mem_filter.mp hP).2
      have hQ_eq :=
        normalizedFactor_eq_ramifiedPrimeIdeal_ramifiedPrimeOfNormalizedFactor d Q
          (Finset.mem_filter.mp hQ).2
      calc
        P.1 =
            ramifiedPrimeIdeal d
              (ramifiedPrimeOfNormalizedFactor d P (Finset.mem_filter.mp hP).2).2 :=
          hP_eq
        _ =
            ramifiedPrimeIdeal d
              (ramifiedPrimeOfNormalizedFactor d Q (Finset.mem_filter.mp hQ).2).2 :=
          congrArg (fun p : {p // p ∈ ramifiedPrimes d} => ramifiedPrimeIdeal d p.2) hpq
        _ = Q.1 := hQ_eq.symm
    · intro p hpT
      have hpMem : ramifiedPrimeIdeal d p.2 ∈ s := (Finset.mem_filter.mp hpT).2
      let P : {P // P ∈ s} := ⟨ramifiedPrimeIdeal d p.2, hpMem⟩
      have hPram : normalizedFactorIsRamified d P :=
        (normalizedFactorIsRamified_iff_exists_eq_ramifiedPrimeIdeal d P).mpr
          ⟨p, rfl⟩
      have hPmem : P ∈ S.filter fun P => normalizedFactorIsRamified d P := by
        rw [Finset.mem_filter]
        exact ⟨by simp [S, P], hPram⟩
      refine ⟨P, hPmem, ?_⟩
      apply Subtype.ext
      have hP_eq :=
        normalizedFactor_eq_ramifiedPrimeIdeal_ramifiedPrimeOfNormalizedFactor d P hPram
      have hIdeal :
          ramifiedPrimeIdeal d (ramifiedPrimeOfNormalizedFactor d P hPram).2 =
            ramifiedPrimeIdeal d p.2 := by
        simpa [P] using hP_eq.symm
      exact (ramifiedPrimeIdeal_eq_iff d
        (ramifiedPrimeOfNormalizedFactor d P hPram).2 p.2).mp hIdeal
    · intro P hP
      have hJ0 : (J : Ideal R) ≠ ⊥ := by
        simpa [Ideal.zero_eq_bot] using mem_nonZeroDivisors_iff_ne_zero.mp J.2
      have hPprime : P.1.IsPrime := (Ideal.mem_normalizedFactors_iff hJ0).mp P.2 |>.1
      have hPram : normalizedFactorIsRamified d P := (Finset.mem_filter.mp hP).2
      let p := ramifiedPrimeOfNormalizedFactor d P hPram
      have hP_eq :
          P.1 = ramifiedPrimeIdeal d p.2 :=
        normalizedFactor_eq_ramifiedPrimeIdeal_ramifiedPrimeOfNormalizedFactor d P hPram
      have hpprime : p.1.Prime := prime_of_mem_ramifiedPrimes p.2
      have hcomap : P.1.comap (algebraMap ℤ R) = 𝔭(p.1) := by
        rw [hP_eq]
        exact (ramifiedPrimeIdeal_mem_primesOver d p.2).2.1.symm
      have hram : Ideal.IsRamifiedIn (𝔭(p.1)) R :=
        ((mem_ramifiedPrimes_iff_isRamifiedIn d p.1).mp p.2).2
      have hnorm : Ideal.absNorm P.1 = p.1 :=
        absNorm_eq_prime_of_isRamifiedIn_of_comap_eq_p d hPprime hpprime hcomap hram
      dsimp [f, term, p]
      rw [hnorm, hP_eq]
  have hright :
      (∏ p ∈ T, term p) =
        Finset.univ.prod fun p : {p // p ∈ ramifiedPrimes d} =>
          p.1 ^
            (UniqueFactorizationMonoid.normalizedFactors
              (J : Ideal (NumberField.RingOfIntegers (Qsqrtd (d : ℚ))))).count
              (ramifiedPrimeIdeal d p.2) := by
    have hfilter :
        (∏ p ∈ Finset.univ with ramifiedPrimeIdeal d p.2 ∈ s, term p) =
          ∏ p : {p // p ∈ ramifiedPrimes d}, term p := by
      refine Finset.prod_filter_of_ne ?_
      intro p _hp hp_ne
      by_contra hmem
      have hcount0 : s.count (ramifiedPrimeIdeal d p.2) = 0 :=
        Multiset.count_eq_zero_of_notMem hmem
      exact hp_ne (by simp [term, hcount0])
    simpa [T, term, s, R] using hfilter
  simpa [f, s, S, R] using hleft.trans hright

private theorem isSquare_ramified_absNorm_count_prod_of_forall_fullRamifiedParityVector_eq_zero
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)]
    (J : (Ideal (NumberField.RingOfIntegers (Qsqrtd (d : ℚ))))⁰)
    (hparity : ∀ p, fullRamifiedParityVector d J p = 0)
    [DecidablePred (fun P :
        {P // P ∈ UniqueFactorizationMonoid.normalizedFactors
          (J : Ideal (NumberField.RingOfIntegers (Qsqrtd (d : ℚ))))} =>
      normalizedFactorIsRamified d P)] :
    IsSquare
      (∏ P ∈
          (UniqueFactorizationMonoid.normalizedFactors
            (J : Ideal (NumberField.RingOfIntegers (Qsqrtd (d : ℚ))))).attach.toFinset with
          normalizedFactorIsRamified d P,
        Ideal.absNorm P.1 ^
          (UniqueFactorizationMonoid.normalizedFactors
            (J : Ideal (NumberField.RingOfIntegers (Qsqrtd (d : ℚ))))).count P.1) := by
  rw [normalizedFactors_ramified_absNorm_count_prod_eq_prime_count_prod d J]
  refine Finset.isSquare_prod _ ?_
  intro p _hp
  exact isSquare_pow_of_two_dvd_nat p.1
    ((UniqueFactorizationMonoid.normalizedFactors
      (J : Ideal (NumberField.RingOfIntegers (Qsqrtd (d : ℚ))))).count
        (ramifiedPrimeIdeal d p.2))
    (two_dvd_count_ramifiedPrimeIdeal_of_fullRamifiedParityVector_eq_zero d J p
      (hparity p))

private theorem isSquare_nonramified_absNorm_count_prod_of_isAmbiguousIdeal
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)]
    (J : (Ideal (NumberField.RingOfIntegers (Qsqrtd (d : ℚ))))⁰)
    (hJ : IsAmbiguousIdeal (conjAutRingOfIntegers (Qsqrtd (d : ℚ)))
      (J : Ideal (NumberField.RingOfIntegers (Qsqrtd (d : ℚ)))))
    [DecidablePred (fun P :
        {P // P ∈ UniqueFactorizationMonoid.normalizedFactors
          (J : Ideal (NumberField.RingOfIntegers (Qsqrtd (d : ℚ))))} =>
      ¬ normalizedFactorIsRamified d P)] :
    IsSquare
      (∏ P ∈
          (UniqueFactorizationMonoid.normalizedFactors
            (J : Ideal (NumberField.RingOfIntegers (Qsqrtd (d : ℚ))))).attach.toFinset with
          ¬ normalizedFactorIsRamified d P,
        Ideal.absNorm P.1 ^
          (UniqueFactorizationMonoid.normalizedFactors
            (J : Ideal (NumberField.RingOfIntegers (Qsqrtd (d : ℚ))))).count P.1) := by
  classical
  let R := NumberField.RingOfIntegers (Qsqrtd (d : ℚ))
  let s := UniqueFactorizationMonoid.normalizedFactors (J : Ideal R)
  let S := s.attach.toFinset.filter fun P => ¬ normalizedFactorIsRamified d P
  let f : {P // P ∈ s} → ℕ := fun P => Ideal.absNorm P.1 ^ s.count P.1
  let σ : {P // P ∈ s} → {P // P ∈ s} := conjAutNormalizedFactor d hJ
  change IsSquare (∏ P ∈ S, f P)
  refine isSquare_finset_prod_of_involution S f σ ?_ ?_ ?_ ?_
  · intro P hP
    rw [Finset.mem_filter] at hP ⊢
    refine ⟨by simp [σ], ?_⟩
    intro hσram
    exact hP.2 ((normalizedFactorIsRamified_conjAutNormalizedFactor_iff d hJ P).mp hσram)
  · intro P _hP
    exact conjAutNormalizedFactor_involutive d hJ P
  · intro P hP hfix
    rw [Finset.mem_filter] at hP
    have hPnonram : ¬ normalizedFactorIsRamified d P := hP.2
    have hJ0 : (J : Ideal R) ≠ ⊥ := by
      simpa [Ideal.zero_eq_bot] using mem_nonZeroDivisors_iff_ne_zero.mp J.2
    have hPdata := (Ideal.mem_normalizedFactors_iff hJ0).mp P.2
    have hP0 : P.1 ≠ ⊥ := by
      intro hPbot
      exact hJ0 (le_bot_iff.mp (by simpa [hPbot] using hPdata.2))
    obtain ⟨p, hp, hcomap, _hdvd⟩ :=
      exists_nat_prime_comap_eq_p_and_dvd_absNorm d hPdata.1 hP0
    rcases factor_contribution_by_splitting_narrowClass d hJ P hp hcomap with
      hsplit | hinert | hram
    · exact False.elim ((conjAutNormalizedFactor_ne_of_isSplitIn d hJ P hp hcomap hsplit.1)
        hfix)
    · have hnorm : Ideal.absNorm P.1 = p ^ 2 :=
        absNorm_eq_prime_sq_of_isInertIn_of_comap_eq_p d hPdata.1 hp hcomap hinert.1
      dsimp [f, s]
      rw [hnorm, ← pow_mul]
      exact isSquare_pow_of_two_dvd_nat p (2 * s.count P.1) ⟨s.count P.1, rfl⟩
    · exact False.elim (hPnonram ⟨p, hp, hcomap, hram.1⟩)
  · intro P hP _hneq
    rw [Finset.mem_filter] at hP
    have hcount :
        s.count (σ P).1 = s.count P.1 := by
      simpa [σ, s, R] using normalizedFactors_count_conjAutNormalizedFactor_eq d hJ P
    have hnorm :
        Ideal.absNorm (σ P).1 = Ideal.absNorm P.1 := by
      change
        Ideal.absNorm
            (Ideal.map (conjAutRingOfIntegers (Qsqrtd (d : ℚ)) : R →+* R) P.1) =
          Ideal.absNorm P.1
      exact Ideal.absNorm_map_equiv (conjAutRingOfIntegers (Qsqrtd (d : ℚ))) P.1
    dsimp [f]
    rw [hcount, hnorm]

private theorem finset_prod_multiset_attach_toFinset_count
    {α M : Type*} [DecidableEq α] [CommMonoid M]
    (s : Multiset α) (f : α → M) :
    (∏ P ∈ s.attach.toFinset, f P.1 ^ s.count P.1) =
      ∏ P ∈ s.toFinset, f P ^ s.count P := by
  classical
  refine Finset.prod_bij (fun P _hP => P.1) ?_ ?_ ?_ ?_
  · intro P _hP
    exact Multiset.mem_toFinset.mpr P.2
  · intro P _hP Q _hQ hPQ
    exact Subtype.ext hPQ
  · intro P hP
    refine ⟨⟨P, Multiset.mem_toFinset.mp hP⟩, ?_, rfl⟩
    simp
  · intro P _hP
    rfl

private theorem absNorm_eq_normalizedFactors_absNorm_count_prod
    {R : Type*} [CommRing R] [Nontrivial R] [IsDedekindDomain R] [Module.Free ℤ R]
    (I : Ideal R) (hI0 : I ≠ ⊥) :
    Ideal.absNorm I =
      ∏ P ∈ (UniqueFactorizationMonoid.normalizedFactors I).attach.toFinset,
        Ideal.absNorm P.1 ^
          (UniqueFactorizationMonoid.normalizedFactors I).count P.1 := by
  let s := UniqueFactorizationMonoid.normalizedFactors I
  calc
    Ideal.absNorm I = Ideal.absNorm s.prod := by
      rw [Ideal.prod_normalizedFactors_eq_self hI0]
    _ = (s.map fun P => Ideal.absNorm P).prod := by
      rw [map_multiset_prod]
    _ = ∏ P ∈ s.attach.toFinset, Ideal.absNorm P.1 ^ s.count P.1 := by
      rw [finset_prod_multiset_attach_toFinset_count]
      exact Finset.prod_multiset_map_count s (fun P => Ideal.absNorm P)

theorem isSquare_absNorm_of_isAmbiguousIdeal_of_forall_fullRamifiedParityVector_eq_zero
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)]
    (J : (Ideal (NumberField.RingOfIntegers (Qsqrtd (d : ℚ))))⁰)
    (hJ : IsAmbiguousIdeal (conjAutRingOfIntegers (Qsqrtd (d : ℚ)))
      (J : Ideal (NumberField.RingOfIntegers (Qsqrtd (d : ℚ)))))
    (hparity : ∀ p, fullRamifiedParityVector d J p = 0) :
    IsSquare (Ideal.absNorm (J : Ideal (NumberField.RingOfIntegers (Qsqrtd (d : ℚ))))) := by
  classical
  let R := NumberField.RingOfIntegers (Qsqrtd (d : ℚ))
  let s := UniqueFactorizationMonoid.normalizedFactors (J : Ideal R)
  let S := s.attach.toFinset
  let f : {P // P ∈ s} → ℕ := fun P => Ideal.absNorm P.1 ^ s.count P.1
  have hJ0 : (J : Ideal R) ≠ ⊥ := by
    simpa [Ideal.zero_eq_bot] using mem_nonZeroDivisors_iff_ne_zero.mp J.2
  have hnorm :
      Ideal.absNorm (J : Ideal R) = ∏ P ∈ S, f P := by
    simpa [S, f, s, R] using
      absNorm_eq_normalizedFactors_absNorm_count_prod (I := (J : Ideal R)) hJ0
  rw [hnorm]
  have hsplit :=
    Finset.prod_filter_mul_prod_filter_not S (fun P => normalizedFactorIsRamified d P) f
  rw [← hsplit]
  exact
    (isSquare_ramified_absNorm_count_prod_of_forall_fullRamifiedParityVector_eq_zero
      d J hparity).mul
    (isSquare_nonramified_absNorm_count_prod_of_isAmbiguousIdeal d J hJ)

private theorem mem_ramifiedPrimes_of_prime_dvd_natAbs
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)]
    {p : ℕ} (hp : p.Prime) (hpdvd : p ∣ d.natAbs) :
    p ∈ ramifiedPrimes d := by
  letI : Fact p.Prime := ⟨hp⟩
  by_cases hp2 : p = 2
  · subst p
    have h2dvd : (2 : ℤ) ∣ d := by
      rw [← Int.dvd_natAbs]
      exact_mod_cast hpdvd
    have hd4 : d % 4 ≠ 1 := by
      intro hd4
      have hnot : ¬ (2 : ℤ) ∣ d := by omega
      exact hnot h2dvd
    exact (mem_ramifiedPrimes_iff_isRamifiedIn d 2).mpr
      ⟨Nat.prime_two, Splitting.isRamified_two_of_mod_four_ne_one d hd4⟩
  · have hpdvd_int : (p : ℤ) ∣ d := by
      rw [← Int.dvd_natAbs]
      exact_mod_cast hpdvd
    have hram : Ideal.IsRamifiedIn (𝔭(p))
        (NumberField.RingOfIntegers (Qsqrtd (d : ℚ))) :=
      Splitting.isRamified_of_odd_dvd d p hp2 hpdvd_int
    exact (mem_ramifiedPrimes_iff_isRamifiedIn d p).mpr ⟨hp, hram⟩

theorem exists_nonzero_fullRamifiedParityVector_span_sqrtdInt_of_ne_neg_one
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] (hdm1 : d ≠ -1) :
    let R := NumberField.RingOfIntegers (Qsqrtd (d : ℚ))
    ∃ p, fullRamifiedParityVector d
      (⟨Ideal.span ({Splitting.sqrtdInt d} : Set R), by
        have hsqrtd_ne : Splitting.sqrtdInt d ≠ 0 := by
          intro h
          have hcoe : ((Splitting.sqrtdInt d : R) : Qsqrtd (d : ℚ)) = 0 := by
            rw [h]
            simp
          rw [Splitting.coe_sqrtdInt] at hcoe
          have him := congrArg QuadraticAlgebra.im hcoe
          norm_num at him
        rw [mem_nonZeroDivisors_iff_ne_zero, Ideal.zero_eq_bot, ne_eq,
          Ideal.span_singleton_eq_bot]
        exact hsqrtd_ne⟩ : (Ideal R)⁰) p ≠ 0 := by
  classical
  let R := NumberField.RingOfIntegers (Qsqrtd (d : ℚ))
  have hsqrtd_ne : Splitting.sqrtdInt d ≠ 0 := by
    intro h
    have hcoe : ((Splitting.sqrtdInt d : R) : Qsqrtd (d : ℚ)) = 0 := by
      rw [h]
      simp
    rw [Splitting.coe_sqrtdInt] at hcoe
    have him := congrArg QuadraticAlgebra.im hcoe
    norm_num at him
  let J : (Ideal R)⁰ :=
    ⟨Ideal.span ({Splitting.sqrtdInt d} : Set R), by
      rw [mem_nonZeroDivisors_iff_ne_zero, Ideal.zero_eq_bot, ne_eq,
        Ideal.span_singleton_eq_bot]
      exact hsqrtd_ne⟩
  have hdabs_ne_one : d.natAbs ≠ 1 := by
    intro h
    obtain hd | hd := Int.natAbs_eq d
    · have hd' : d = 1 := by omega
      exact (Fact.out : d ≠ 1) hd'
    · have hd' : d = -1 := by omega
      exact hdm1 hd'
  obtain ⟨p, hp, hpdvd⟩ := Nat.exists_prime_and_dvd hdabs_ne_one
  have hpRam : p ∈ ramifiedPrimes d := mem_ramifiedPrimes_of_prime_dvd_natAbs d hp hpdvd
  let pr : {p // p ∈ ramifiedPrimes d} := ⟨p, hpRam⟩
  by_contra hnone
  have hzero : fullRamifiedParityVector d J pr = 0 := by
    by_contra hne
    exact hnone ⟨pr, hne⟩
  have hJ0 : (J : Ideal R) ≠ ⊥ := by
    exact mem_nonZeroDivisors_iff_ne_zero.mp J.2
  have hnormJ : Ideal.absNorm (J : Ideal R) = d.natAbs := by
    simpa [J, R] using absNorm_span_sqrtdInt d
  have hpdivJ : p ∣ Ideal.absNorm (J : Ideal R) := by
    rw [hnormJ]
    exact hpdvd
  obtain ⟨P, hPmem, hPover⟩ :=
    exists_normalizedFactor_mem_primesOver_of_nat_prime_dvd_absNorm hJ0 hp hpdivJ
  have hP_eq : P = ramifiedPrimeIdeal d hpRam := by
    rw [primesOver_eq_singleton_ramifiedPrimeIdeal d hpRam] at hPover
    simpa using hPover
  have hramMem : ramifiedPrimeIdeal d hpRam ∈
      UniqueFactorizationMonoid.normalizedFactors (J : Ideal R) := by
    simpa [hP_eq] using hPmem
  have hcount2 :=
    two_le_count_of_fullRamifiedParityVector_eq_zero_of_mem d J pr hzero hramMem
  have hnorm_sq_dvd :
      Ideal.absNorm (ramifiedPrimeIdeal d hpRam) ^ 2 ∣ Ideal.absNorm (J : Ideal R) :=
    absNorm_sq_dvd_of_two_le_normalizedFactors_count hJ0 hcount2
  have hp_dvd_normP := nat_prime_dvd_absNorm_ramifiedPrimeIdeal d hpRam
  have hnot := not_absNorm_sq_dvd_squarefree_natAbs
    (Fact.out : Squarefree d) hp hp_dvd_normP
  rw [hnormJ] at hnorm_sq_dvd
  exact hnot hnorm_sq_dvd

private theorem normalizedFactors_count_prod_eq_ramifiedPrime_count_prod_of_isAmbiguousIdeal'
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)]
    (J : (Ideal (NumberField.RingOfIntegers (Qsqrtd (d : ℚ))))⁰)
    (hJ : IsAmbiguousIdeal (conjAutRingOfIntegers (Qsqrtd (d : ℚ)))
      (J : Ideal (NumberField.RingOfIntegers (Qsqrtd (d : ℚ))))) :
    (∏ P ∈
        (UniqueFactorizationMonoid.normalizedFactors
          (J : Ideal (NumberField.RingOfIntegers (Qsqrtd (d : ℚ))))).attach.toFinset,
      (NarrowClassGroup.mk0 (normalizedFactorNonzeroIdeal J P) :
        NarrowClassGroup (NumberField.RingOfIntegers (Qsqrtd (d : ℚ)))) ^
        (UniqueFactorizationMonoid.normalizedFactors
          (J : Ideal (NumberField.RingOfIntegers (Qsqrtd (d : ℚ))))).count P.1) =
      Finset.univ.prod fun p : {p // p ∈ ramifiedPrimes d} =>
        (ramifiedPrimeNarrowClass d p.2) ^
          (UniqueFactorizationMonoid.normalizedFactors
            (J : Ideal (NumberField.RingOfIntegers (Qsqrtd (d : ℚ))))).count
            (ramifiedPrimeIdeal d p.2) := by
  classical
  let R := NumberField.RingOfIntegers (Qsqrtd (d : ℚ))
  let s := UniqueFactorizationMonoid.normalizedFactors (J : Ideal R)
  let S := s.attach.toFinset
  let f : {P // P ∈ s} → NarrowClassGroup R := fun P =>
    (NarrowClassGroup.mk0 (normalizedFactorNonzeroIdeal J P) :
        NarrowClassGroup R) ^ s.count P.1
  have hnonram :
      (∏ P ∈ S with ¬ normalizedFactorIsRamified d P, f P) = 1 := by
    simpa [S, f, s, R] using
      normalizedFactors_nonramified_count_prod_eq_one_of_isAmbiguousIdeal d J hJ
  have hram :
      (∏ P ∈ S with normalizedFactorIsRamified d P, f P) =
        Finset.univ.prod fun p : {p // p ∈ ramifiedPrimes d} =>
          (ramifiedPrimeNarrowClass d p.2) ^
            (UniqueFactorizationMonoid.normalizedFactors
              (J : Ideal (NumberField.RingOfIntegers (Qsqrtd (d : ℚ))))).count
              (ramifiedPrimeIdeal d p.2) := by
    simpa [S, f, s, R] using
      normalizedFactors_ramified_count_prod_eq_ramifiedPrime_count_prod d J
  calc
    (∏ P ∈ S, f P) =
        (∏ P ∈ S with ¬ normalizedFactorIsRamified d P, f P) *
          ∏ P ∈ S with normalizedFactorIsRamified d P, f P := by
      exact (Finset.prod_filter_not_mul_prod_filter S
        (fun P => normalizedFactorIsRamified d P) f).symm
    _ = Finset.univ.prod fun p : {p // p ∈ ramifiedPrimes d} =>
          (ramifiedPrimeNarrowClass d p.2) ^
            (UniqueFactorizationMonoid.normalizedFactors
              (J : Ideal (NumberField.RingOfIntegers (Qsqrtd (d : ℚ))))).count
              (ramifiedPrimeIdeal d p.2) := by
      rw [hnonram, hram, one_mul]

theorem ambiguousIdeal_mk0_eq_fullRamifiedParityIdealProduct_of_factorization'
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)]
    (J : (Ideal (NumberField.RingOfIntegers (Qsqrtd (d : ℚ))))⁰)
    (hJ : IsAmbiguousIdeal (conjAutRingOfIntegers (Qsqrtd (d : ℚ)))
      (J : Ideal (NumberField.RingOfIntegers (Qsqrtd (d : ℚ))))) :
    NarrowClassGroup.mk0 J =
      NarrowClassGroup.mk0
        (fullRamifiedParityIdealProduct d (fullRamifiedParityVector d J)) := by
  have hJ_factorization_count :=
    narrowClassGroup_mk0_eq_normalizedFactors_attach_toFinset_prod J
  have htarget_count :
      NarrowClassGroup.mk0
          (fullRamifiedParityIdealProduct d (fullRamifiedParityVector d J)) =
        Finset.univ.prod fun p : {p // p ∈ ramifiedPrimes d} =>
          (ramifiedPrimeNarrowClass d p.2) ^
            (UniqueFactorizationMonoid.normalizedFactors
              (J : Ideal (NumberField.RingOfIntegers (Qsqrtd (d : ℚ))))).count
              (ramifiedPrimeIdeal d p.2) := by
    rw [mk0_fullRamifiedParityIdealProduct]
    exact fullRamifiedParityNarrowClassProduct_eq_ramifiedPrime_count_prod d J
  calc
    NarrowClassGroup.mk0 J =
        ∏ P ∈
            (UniqueFactorizationMonoid.normalizedFactors
              (J : Ideal (NumberField.RingOfIntegers (Qsqrtd (d : ℚ))))).attach.toFinset,
          (NarrowClassGroup.mk0 (normalizedFactorNonzeroIdeal J P) :
            NarrowClassGroup (NumberField.RingOfIntegers (Qsqrtd (d : ℚ)))) ^
            (UniqueFactorizationMonoid.normalizedFactors
              (J : Ideal (NumberField.RingOfIntegers (Qsqrtd (d : ℚ))))).count P.1 := by
      exact hJ_factorization_count
    _ = Finset.univ.prod fun p : {p // p ∈ ramifiedPrimes d} =>
          (ramifiedPrimeNarrowClass d p.2) ^
            (UniqueFactorizationMonoid.normalizedFactors
              (J : Ideal (NumberField.RingOfIntegers (Qsqrtd (d : ℚ))))).count
              (ramifiedPrimeIdeal d p.2) := by
      exact normalizedFactors_count_prod_eq_ramifiedPrime_count_prod_of_isAmbiguousIdeal' d J hJ
    _ = NarrowClassGroup.mk0
          (fullRamifiedParityIdealProduct d (fullRamifiedParityVector d J)) :=
      htarget_count.symm

end Internal
end GenusTheory
end ClassGroup
end QuadraticNumberFields
