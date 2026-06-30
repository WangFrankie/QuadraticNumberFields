/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/

import QuadraticNumberFields.ClassGroup.GenusTheory.AmbiguousIdeals.Conjugation
import QuadraticNumberFields.Splitting.Qsqrtd.SqrtD

/-!
# Ramified Parity Products

This file builds the ramified-prime parity vectors and products used in the
ambiguous-ideal upper bound.
-/

namespace QuadraticNumberFields
namespace ClassGroup
namespace GenusTheory

open scoped nonZeroDivisors NumberField Pointwise QuadraticNumberFields.ClassGroup
open scoped QuadraticNumberFields.Splitting

attribute [-instance] DivisionRing.toRatAlgebra
attribute [local instance] FractionRing.liftAlgebra

namespace Internal

noncomputable def idealRamifiedParityVector
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)]
    {p0 : ℕ} (_hp0 : p0 ∈ ramifiedPrimes d)
    (I : (Ideal (NumberField.RingOfIntegers (Qsqrtd (d : ℚ))))⁰) :
    ({p // p ∈ (ramifiedPrimes d).erase p0} → Fin 2) := by
  classical
  exact fun p =>
    ⟨(UniqueFactorizationMonoid.normalizedFactors I.1).count
        (ramifiedPrimeIdeal d ((Finset.mem_erase.mp p.2).2)) % 2,
      Nat.mod_lt _ (by decide : 0 < 2)⟩

noncomputable def ramifiedPrimeNarrowClass
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)]
    {p : ℕ} (hp : p ∈ ramifiedPrimes d) :
    NarrowClassGroup (NumberField.RingOfIntegers (Qsqrtd (d : ℚ))) :=
  NarrowClassGroup.mk0
    ⟨ramifiedPrimeIdeal d hp,
      mem_nonZeroDivisors_iff_ne_zero.mpr (by
        simpa [Ideal.zero_eq_bot] using ramifiedPrimeIdeal_ne_bot d hp)⟩

noncomputable def ramifiedParityIdealProduct
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)]
    {p0 : ℕ} (_hp0 : p0 ∈ ramifiedPrimes d)
    (v : ({p // p ∈ (ramifiedPrimes d).erase p0} → Fin 2)) :
    (Ideal (NumberField.RingOfIntegers (Qsqrtd (d : ℚ))))⁰ := by
  classical
  exact Finset.univ.prod fun p : {p // p ∈ (ramifiedPrimes d).erase p0} =>
    if v p = 0 then 1 else
      ⟨ramifiedPrimeIdeal d ((Finset.mem_erase.mp p.2).2),
        mem_nonZeroDivisors_iff_ne_zero.mpr (by
          simpa [Ideal.zero_eq_bot] using
            ramifiedPrimeIdeal_ne_bot d ((Finset.mem_erase.mp p.2).2))⟩

noncomputable def fullRamifiedParityVector
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)]
    (I : (Ideal (NumberField.RingOfIntegers (Qsqrtd (d : ℚ))))⁰) :
    ({p // p ∈ ramifiedPrimes d} → Fin 2) := by
  classical
  exact fun p =>
    ⟨(UniqueFactorizationMonoid.normalizedFactors I.1).count
        (ramifiedPrimeIdeal d p.2) % 2,
      Nat.mod_lt _ (by decide : 0 < 2)⟩

noncomputable def fullRamifiedParityIdealProduct
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)]
    (v : ({p // p ∈ ramifiedPrimes d} → Fin 2)) :
    (Ideal (NumberField.RingOfIntegers (Qsqrtd (d : ℚ))))⁰ := by
  classical
  exact Finset.univ.prod fun p : {p // p ∈ ramifiedPrimes d} =>
    if v p = 0 then 1 else
      ⟨ramifiedPrimeIdeal d p.2,
        mem_nonZeroDivisors_iff_ne_zero.mpr (by
          simpa [Ideal.zero_eq_bot] using ramifiedPrimeIdeal_ne_bot d p.2)⟩

/-- The full ramified parity ideal product of the zero parity vector is the unit
ideal. -/
private theorem fullRamifiedParityIdealProduct_eq_one_of_forall_eq_zero
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)]
    {v : ({p // p ∈ ramifiedPrimes d} → Fin 2)} (hv : ∀ p, v p = 0) :
    fullRamifiedParityIdealProduct d v =
      (1 : (Ideal (NumberField.RingOfIntegers (Qsqrtd (d : ℚ))))⁰) := by
  classical
  simp [fullRamifiedParityIdealProduct, hv]

/-- A ramified prime ideal is fixed by quadratic conjugation. -/
theorem isAmbiguousIdeal_ramifiedPrimeIdeal
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)]
    {p : ℕ} (hp : p ∈ ramifiedPrimes d) :
    IsAmbiguousIdeal
      (conjAutRingOfIntegers (Qsqrtd (d : ℚ)))
      (ramifiedPrimeIdeal d hp) :=
  map_conjAut_eq_of_mem_primesOver_of_mem_ramifiedPrimes (d := d) hp
    (ramifiedPrimeIdeal_mem_primesOver d hp)

/-- The full ramified parity ideal product is fixed by quadratic conjugation. -/
theorem isAmbiguousIdeal_fullRamifiedParityIdealProduct
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)]
    (v : ({p // p ∈ ramifiedPrimes d} → Fin 2)) :
    IsAmbiguousIdeal
      (conjAutRingOfIntegers (Qsqrtd (d : ℚ)))
      (fullRamifiedParityIdealProduct d v : Ideal
        (NumberField.RingOfIntegers (Qsqrtd (d : ℚ)))) := by
  classical
  let R := NumberField.RingOfIntegers (Qsqrtd (d : ℚ))
  refine Finset.prod_induction
    (s := Finset.univ)
    (f := fun p : {p // p ∈ ramifiedPrimes d} =>
      if v p = 0 then (1 : (Ideal R)⁰) else
        ⟨ramifiedPrimeIdeal d p.2,
          mem_nonZeroDivisors_iff_ne_zero.mpr (by
            simpa [Ideal.zero_eq_bot] using ramifiedPrimeIdeal_ne_bot d p.2)⟩)
    (p := fun I : (Ideal R)⁰ =>
      IsAmbiguousIdeal (conjAutRingOfIntegers (Qsqrtd (d : ℚ)))
        (I : Ideal R))
    ?_ ?_ ?_
  · intro I J hI hJ
    change IsAmbiguousIdeal (conjAutRingOfIntegers (Qsqrtd (d : ℚ)))
      ((I : Ideal R) * (J : Ideal R))
    exact hI.mul hJ
  · simp
  · intro p _hp
    by_cases hpv : v p = 0
    · simp [hpv]
    · simp [hpv, isAmbiguousIdeal_ramifiedPrimeIdeal]

/-- The ramified parity ideal product is fixed by quadratic conjugation. -/
theorem isAmbiguousIdeal_ramifiedParityIdealProduct
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)]
    {p0 : ℕ} (hp0 : p0 ∈ ramifiedPrimes d)
    (v : ({p // p ∈ (ramifiedPrimes d).erase p0} → Fin 2)) :
    IsAmbiguousIdeal
      (conjAutRingOfIntegers (Qsqrtd (d : ℚ)))
      (ramifiedParityIdealProduct d hp0 v : Ideal
        (NumberField.RingOfIntegers (Qsqrtd (d : ℚ)))) := by
  classical
  let R := NumberField.RingOfIntegers (Qsqrtd (d : ℚ))
  refine Finset.prod_induction
    (s := Finset.univ)
    (f := fun p : {p // p ∈ (ramifiedPrimes d).erase p0} =>
      if v p = 0 then (1 : (Ideal R)⁰) else
        ⟨ramifiedPrimeIdeal d ((Finset.mem_erase.mp p.2).2),
          mem_nonZeroDivisors_iff_ne_zero.mpr (by
            simpa [Ideal.zero_eq_bot] using
              ramifiedPrimeIdeal_ne_bot d ((Finset.mem_erase.mp p.2).2))⟩)
    (p := fun I : (Ideal R)⁰ =>
      IsAmbiguousIdeal (conjAutRingOfIntegers (Qsqrtd (d : ℚ)))
        (I : Ideal R))
    ?_ ?_ ?_
  · intro I J hI hJ
    change IsAmbiguousIdeal (conjAutRingOfIntegers (Qsqrtd (d : ℚ)))
      ((I : Ideal R) * (J : Ideal R))
    exact hI.mul hJ
  · simp
  · intro p _hp
    by_cases hpv : v p = 0
    · simp [hpv]
    · simp [hpv, isAmbiguousIdeal_ramifiedPrimeIdeal]

theorem toClassGroup_ramifiedPrimeNarrowClass
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)]
    {p : ℕ} (hp : p ∈ ramifiedPrimes d) :
    NarrowClassGroup.toClassGroup (NumberField.RingOfIntegers (Qsqrtd (d : ℚ)))
        (ramifiedPrimeNarrowClass d hp) =
      ClassGroup.mk0
        (⟨ramifiedPrimeIdeal d hp,
          mem_nonZeroDivisors_iff_ne_zero.mpr (by
            simpa [Ideal.zero_eq_bot] using ramifiedPrimeIdeal_ne_bot d hp)⟩ :
          (Ideal (NumberField.RingOfIntegers (Qsqrtd (d : ℚ))))⁰) := by
  simp [ramifiedPrimeNarrowClass]

theorem classGroup_mk0_sq_eq_one_ramifiedPrimeIdeal
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)]
    {p : ℕ} (hp : p ∈ ramifiedPrimes d) :
    (ClassGroup.mk0
        (⟨ramifiedPrimeIdeal d hp,
          mem_nonZeroDivisors_iff_ne_zero.mpr (by
            simpa [Ideal.zero_eq_bot] using ramifiedPrimeIdeal_ne_bot d hp)⟩ :
          (Ideal (NumberField.RingOfIntegers (Qsqrtd (d : ℚ))))⁰) :
        ClassGroup (NumberField.RingOfIntegers (Qsqrtd (d : ℚ)))) ^ 2 = 1 := by
  let R := NumberField.RingOfIntegers (Qsqrtd (d : ℚ))
  have hpPrime : p.Prime := prime_of_mem_ramifiedPrimes hp
  have hram :
      Ideal.IsRamifiedIn (𝔭(p)) R :=
    ((mem_ramifiedPrimes_iff_isRamifiedIn d p).mp hp).2
  have hP2 :
      ((ramifiedPrimeIdeal d hp) ^ 2).IsPrincipal := by
    rw [← map_span_eq_sq_of_isRamifiedIn_of_mem_primesOver (d := d)
      hpPrime (ramifiedPrimeIdeal_mem_primesOver d hp) hram]
    rw [Ideal.map_span, Set.image_singleton]
    exact ⟨_, rfl⟩
  exact classGroup_mk0_sq_eq_one_of_sq_isPrincipal (ramifiedPrimeIdeal_ne_bot d hp) hP2

theorem isTotallyPositive_natCast_fractionRing
    {R : Type*} [CommRing R] [IsDomain R] (n : ℕ) (hn : 0 < n) :
    NarrowClassGroup.IsTotallyPositive
      (algebraMap R (FractionRing R) (n : R)) := by
  intro σ
  have hσ : σ (algebraMap R (FractionRing R) (n : R)) = (n : ℝ) := by
    exact map_natCast (σ.comp (algebraMap R (FractionRing R))) n
  rw [hσ]
  exact Nat.cast_pos.mpr hn

theorem narrowClassGroup_mk0_span_singleton_eq_one_of_isTotallyPositive
    {R : Type*} [CommRing R] [IsDomain R] [IsDedekindDomain R]
    {a : R} (ha : a ≠ 0)
    (hpos : NarrowClassGroup.IsTotallyPositive (algebraMap R (FractionRing R) a)) :
    NarrowClassGroup.mk0
      (R := R)
      ⟨Ideal.span ({a} : Set R), by
        rw [mem_nonZeroDivisors_iff_ne_zero, Ideal.zero_eq_bot, ne_eq,
          Ideal.span_singleton_eq_bot]
        exact ha⟩ = 1 := by
  let K := FractionRing R
  have haK : algebraMap R K a ≠ 0 := by
    rw [ne_eq, FaithfulSMul.algebraMap_eq_zero_iff]
    exact ha
  let u : Kˣ := Units.mk0 (algebraMap R K a) haK
  have hu_pos : u ∈ NarrowClassGroup.totallyPositiveUnits K := hpos
  rw [← NarrowClassGroup.mk_mk0, NarrowClassGroup.mk_eq_mk']
  exact (QuotientGroup.eq_one_iff _).mpr ⟨⟨u, hu_pos⟩, by
    apply Units.ext
    change (toPrincipalIdeal R K u : FractionalIdeal R⁰ K) =
      FractionalIdeal.mk0 K
        ⟨Ideal.span ({a} : Set R), by
          rw [mem_nonZeroDivisors_iff_ne_zero, Ideal.zero_eq_bot, ne_eq,
            Ideal.span_singleton_eq_bot]
          exact ha⟩
    rw [coe_toPrincipalIdeal]
    change FractionalIdeal.spanSingleton R⁰ (algebraMap R K a) =
      (Ideal.span ({a} : Set R) : FractionalIdeal R⁰ K)
    rw [FractionalIdeal.coeIdeal_span_singleton]⟩

/-- A Dedekind prime factor of a nonzero integral ideal, regarded as a nonzero
ideal. The nonzeroness follows from containment of the original nonzero ideal
in the prime factor. -/
def normalizedFactorNonzeroIdeal
    {R : Type*} [CommRing R] [IsDomain R] [IsDedekindDomain R]
    (I : (Ideal R)⁰)
    (P : {P // P ∈ UniqueFactorizationMonoid.normalizedFactors (I : Ideal R)}) :
    (Ideal R)⁰ :=
  ⟨P.1, mem_nonZeroDivisors_iff_ne_zero.mpr (by
    have hI0 : (I : Ideal R) ≠ ⊥ := by
      simpa [Ideal.zero_eq_bot] using mem_nonZeroDivisors_iff_ne_zero.mp I.2
    have hPdata := (Ideal.mem_normalizedFactors_iff hI0).mp P.2
    intro hPbot
    exact hI0 (le_bot_iff.mp (by simpa [hPbot] using hPdata.2)))⟩

/-- A normalized prime factor of an ideal lies over a ramified rational prime. -/
def normalizedFactorIsRamified
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)]
    {I : (Ideal (NumberField.RingOfIntegers (Qsqrtd (d : ℚ))))⁰}
    (P : {P // P ∈ UniqueFactorizationMonoid.normalizedFactors
      (I : Ideal (NumberField.RingOfIntegers (Qsqrtd (d : ℚ))))}) :
    Prop :=
  ∃ p : ℕ, p.Prime ∧
    P.1.comap (algebraMap ℤ (NumberField.RingOfIntegers (Qsqrtd (d : ℚ)))) =
      𝔭(p) ∧
    Ideal.IsRamifiedIn (𝔭(p)) (NumberField.RingOfIntegers (Qsqrtd (d : ℚ)))

/-- Conjugation acts on the normalized prime factors of an ambiguous ideal. -/
noncomputable def conjAutNormalizedFactor
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)]
    {I : (Ideal (NumberField.RingOfIntegers (Qsqrtd (d : ℚ))))⁰}
    (hI : IsAmbiguousIdeal (conjAutRingOfIntegers (Qsqrtd (d : ℚ)))
      (I : Ideal (NumberField.RingOfIntegers (Qsqrtd (d : ℚ)))))
    (P : {P // P ∈ UniqueFactorizationMonoid.normalizedFactors
      (I : Ideal (NumberField.RingOfIntegers (Qsqrtd (d : ℚ))))}) :
    {P // P ∈ UniqueFactorizationMonoid.normalizedFactors
      (I : Ideal (NumberField.RingOfIntegers (Qsqrtd (d : ℚ))))} := by
  let R := NumberField.RingOfIntegers (Qsqrtd (d : ℚ))
  have hI0 : (I : Ideal R) ≠ ⊥ := by
    simpa [Ideal.zero_eq_bot] using mem_nonZeroDivisors_iff_ne_zero.mp I.2
  exact
    ⟨Ideal.map (conjAutRingOfIntegers (Qsqrtd (d : ℚ)) : R →+* R) P.1,
      (map_conjAut_mem_normalizedFactors_iff_of_isAmbiguousIdeal
        (K := Qsqrtd (d : ℚ)) (P := P.1) (I := (I : Ideal R)) hI0 hI).mpr P.2⟩

theorem conjAutNormalizedFactor_involutive
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)]
    {I : (Ideal (NumberField.RingOfIntegers (Qsqrtd (d : ℚ))))⁰}
    (hI : IsAmbiguousIdeal (conjAutRingOfIntegers (Qsqrtd (d : ℚ)))
      (I : Ideal (NumberField.RingOfIntegers (Qsqrtd (d : ℚ)))))
    (P : {P // P ∈ UniqueFactorizationMonoid.normalizedFactors
      (I : Ideal (NumberField.RingOfIntegers (Qsqrtd (d : ℚ))))}) :
    conjAutNormalizedFactor d hI (conjAutNormalizedFactor d hI P) = P := by
  apply Subtype.ext
  exact map_conjAut_map_conjAut (Qsqrtd (d : ℚ)) P.1

theorem conjAutNormalizedFactor_comap_eq
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)]
    {I : (Ideal (NumberField.RingOfIntegers (Qsqrtd (d : ℚ))))⁰}
    (hI : IsAmbiguousIdeal (conjAutRingOfIntegers (Qsqrtd (d : ℚ)))
      (I : Ideal (NumberField.RingOfIntegers (Qsqrtd (d : ℚ)))))
    (P : {P // P ∈ UniqueFactorizationMonoid.normalizedFactors
      (I : Ideal (NumberField.RingOfIntegers (Qsqrtd (d : ℚ))))}) :
    (conjAutNormalizedFactor d hI P).1.comap
        (algebraMap ℤ (NumberField.RingOfIntegers (Qsqrtd (d : ℚ)))) =
      P.1.comap (algebraMap ℤ (NumberField.RingOfIntegers (Qsqrtd (d : ℚ)))) := by
  let R := NumberField.RingOfIntegers (Qsqrtd (d : ℚ))
  have hlies :=
    map_conjAut_liesOver_comap (K := Qsqrtd (d : ℚ)) P.1
  change
    (Ideal.map (conjAutRingOfIntegers (Qsqrtd (d : ℚ)) : R →+* R) P.1).comap
        (algebraMap ℤ R) =
      P.1.comap (algebraMap ℤ R)
  rw [← Ideal.under_def]
  exact hlies.over.symm

theorem normalizedFactorIsRamified_conjAutNormalizedFactor_iff
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)]
    {I : (Ideal (NumberField.RingOfIntegers (Qsqrtd (d : ℚ))))⁰}
    (hI : IsAmbiguousIdeal (conjAutRingOfIntegers (Qsqrtd (d : ℚ)))
      (I : Ideal (NumberField.RingOfIntegers (Qsqrtd (d : ℚ)))))
    (P : {P // P ∈ UniqueFactorizationMonoid.normalizedFactors
      (I : Ideal (NumberField.RingOfIntegers (Qsqrtd (d : ℚ))))}) :
    normalizedFactorIsRamified d (conjAutNormalizedFactor d hI P) ↔
      normalizedFactorIsRamified d P := by
  constructor
  · rintro ⟨p, hp, hcomap, hram⟩
    refine ⟨p, hp, ?_, hram⟩
    rw [← conjAutNormalizedFactor_comap_eq d hI P]
    exact hcomap
  · rintro ⟨p, hp, hcomap, hram⟩
    refine ⟨p, hp, ?_, hram⟩
    rw [conjAutNormalizedFactor_comap_eq d hI P]
    exact hcomap

theorem normalizedFactors_count_conjAutNormalizedFactor_eq
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)]
    {I : (Ideal (NumberField.RingOfIntegers (Qsqrtd (d : ℚ))))⁰}
    (hI : IsAmbiguousIdeal (conjAutRingOfIntegers (Qsqrtd (d : ℚ)))
      (I : Ideal (NumberField.RingOfIntegers (Qsqrtd (d : ℚ)))))
    (P : {P // P ∈ UniqueFactorizationMonoid.normalizedFactors
      (I : Ideal (NumberField.RingOfIntegers (Qsqrtd (d : ℚ))))}) :
    (UniqueFactorizationMonoid.normalizedFactors
        (I : Ideal (NumberField.RingOfIntegers (Qsqrtd (d : ℚ))))).count
      (conjAutNormalizedFactor d hI P).1 =
    (UniqueFactorizationMonoid.normalizedFactors
        (I : Ideal (NumberField.RingOfIntegers (Qsqrtd (d : ℚ))))).count P.1 := by
  let R := NumberField.RingOfIntegers (Qsqrtd (d : ℚ))
  have hI0 : (I : Ideal R) ≠ ⊥ := by
    simpa [Ideal.zero_eq_bot] using mem_nonZeroDivisors_iff_ne_zero.mp I.2
  exact
    map_conjAut_count_normalizedFactors_eq_of_isAmbiguousIdeal
      (K := Qsqrtd (d : ℚ)) (P := P.1) (I := (I : Ideal R)) hI0 hI

theorem conjAutNormalizedFactor_ne_of_isSplitIn
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)]
    {I : (Ideal (NumberField.RingOfIntegers (Qsqrtd (d : ℚ))))⁰}
    (hI : IsAmbiguousIdeal (conjAutRingOfIntegers (Qsqrtd (d : ℚ)))
      (I : Ideal (NumberField.RingOfIntegers (Qsqrtd (d : ℚ)))))
    (P : {P // P ∈ UniqueFactorizationMonoid.normalizedFactors
      (I : Ideal (NumberField.RingOfIntegers (Qsqrtd (d : ℚ))))})
    {p : ℕ} (hp : p.Prime)
    (hcomap : P.1.comap
      (algebraMap ℤ (NumberField.RingOfIntegers (Qsqrtd (d : ℚ)))) = 𝔭(p))
    (hsplit : Ideal.IsSplitIn (𝔭(p))
      (NumberField.RingOfIntegers (Qsqrtd (d : ℚ)))) :
    conjAutNormalizedFactor d hI P ≠ P := by
  let R := NumberField.RingOfIntegers (Qsqrtd (d : ℚ))
  have hI0 : (I : Ideal R) ≠ ⊥ := by
    simpa [Ideal.zero_eq_bot] using mem_nonZeroDivisors_iff_ne_zero.mp I.2
  have hPprime : P.1.IsPrime := (Ideal.mem_normalizedFactors_iff hI0).mp P.2 |>.1
  have hPover : P.1 ∈ Ideal.primesOver (𝔭(p)) R := ⟨hPprime, ⟨hcomap.symm⟩⟩
  have hpbot : (𝔭(p)) ≠ (⊥ : Ideal ℤ) := by
    rw [Ne, Ideal.span_singleton_eq_bot, Nat.cast_eq_zero]
    exact hp.ne_zero
  haveI : (𝔭(p)).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible
      ((Nat.prime_iff_prime_int.mp hp).irreducible)
  have hne :=
    map_conjAut_ne_of_mem_primesOver_of_isSplitIn
      (K := Qsqrtd (d : ℚ)) (p := 𝔭(p)) hpbot hPover hsplit
  intro hfix
  exact hne (congrArg Subtype.val hfix)

theorem normalizedFactor_eq_ramifiedPrimeIdeal_of_isRamifiedIn
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)]
    {I : (Ideal (NumberField.RingOfIntegers (Qsqrtd (d : ℚ))))⁰}
    (P : {P // P ∈ UniqueFactorizationMonoid.normalizedFactors
      (I : Ideal (NumberField.RingOfIntegers (Qsqrtd (d : ℚ))))})
    {p : ℕ} (hp : p.Prime)
    (hcomap : P.1.comap
      (algebraMap ℤ (NumberField.RingOfIntegers (Qsqrtd (d : ℚ)))) = 𝔭(p))
    (hram : Ideal.IsRamifiedIn (𝔭(p))
      (NumberField.RingOfIntegers (Qsqrtd (d : ℚ)))) :
    ∃ hpRamified : p ∈ ramifiedPrimes d, P.1 = ramifiedPrimeIdeal d hpRamified := by
  let R := NumberField.RingOfIntegers (Qsqrtd (d : ℚ))
  have hpRamified : p ∈ ramifiedPrimes d :=
    (mem_ramifiedPrimes_iff_isRamifiedIn d p).mpr ⟨hp, hram⟩
  have hI0 : (I : Ideal R) ≠ ⊥ := by
    simpa [Ideal.zero_eq_bot] using mem_nonZeroDivisors_iff_ne_zero.mp I.2
  have hPprime : P.1.IsPrime := (Ideal.mem_normalizedFactors_iff hI0).mp P.2 |>.1
  have hPover : P.1 ∈ Ideal.primesOver (𝔭(p)) R := ⟨hPprime, ⟨hcomap.symm⟩⟩
  rw [primesOver_eq_singleton_ramifiedPrimeIdeal d hpRamified] at hPover
  exact ⟨hpRamified, by simpa using hPover⟩

theorem normalizedFactorIsRamified_iff_exists_eq_ramifiedPrimeIdeal
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)]
    {I : (Ideal (NumberField.RingOfIntegers (Qsqrtd (d : ℚ))))⁰}
    (P : {P // P ∈ UniqueFactorizationMonoid.normalizedFactors
      (I : Ideal (NumberField.RingOfIntegers (Qsqrtd (d : ℚ))))}) :
    normalizedFactorIsRamified d P ↔
      ∃ p : {p // p ∈ ramifiedPrimes d}, P.1 = ramifiedPrimeIdeal d p.2 := by
  constructor
  · rintro ⟨p, hp, hcomap, hram⟩
    obtain ⟨hpRamified, hP⟩ :=
      normalizedFactor_eq_ramifiedPrimeIdeal_of_isRamifiedIn d P hp hcomap hram
    exact ⟨⟨p, hpRamified⟩, hP⟩
  · rintro ⟨p, hP⟩
    refine ⟨p.1, prime_of_mem_ramifiedPrimes p.2, ?_, ?_⟩
    · rw [hP]
      exact (ramifiedPrimeIdeal_mem_primesOver d p.2).2.1.symm
    · exact ((mem_ramifiedPrimes_iff_isRamifiedIn d p.1).mp p.2).2

noncomputable def ramifiedPrimeOfNormalizedFactor
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)]
    {I : (Ideal (NumberField.RingOfIntegers (Qsqrtd (d : ℚ))))⁰}
    (P : {P // P ∈ UniqueFactorizationMonoid.normalizedFactors
      (I : Ideal (NumberField.RingOfIntegers (Qsqrtd (d : ℚ))))})
    (hP : normalizedFactorIsRamified d P) :
    {p // p ∈ ramifiedPrimes d} :=
  Classical.choose ((normalizedFactorIsRamified_iff_exists_eq_ramifiedPrimeIdeal d P).mp hP)

theorem normalizedFactor_eq_ramifiedPrimeIdeal_ramifiedPrimeOfNormalizedFactor
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)]
    {I : (Ideal (NumberField.RingOfIntegers (Qsqrtd (d : ℚ))))⁰}
    (P : {P // P ∈ UniqueFactorizationMonoid.normalizedFactors
      (I : Ideal (NumberField.RingOfIntegers (Qsqrtd (d : ℚ))))})
    (hP : normalizedFactorIsRamified d P) :
    P.1 = ramifiedPrimeIdeal d (ramifiedPrimeOfNormalizedFactor d P hP).2 :=
  Classical.choose_spec
    ((normalizedFactorIsRamified_iff_exists_eq_ramifiedPrimeIdeal d P).mp hP)

private theorem normalizedFactorNonzeroIdeal_conjAutNormalizedFactor
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)]
    {I : (Ideal (NumberField.RingOfIntegers (Qsqrtd (d : ℚ))))⁰}
    (hI : IsAmbiguousIdeal (conjAutRingOfIntegers (Qsqrtd (d : ℚ)))
      (I : Ideal (NumberField.RingOfIntegers (Qsqrtd (d : ℚ)))))
    (P : {P // P ∈ UniqueFactorizationMonoid.normalizedFactors
      (I : Ideal (NumberField.RingOfIntegers (Qsqrtd (d : ℚ))))}) :
    normalizedFactorNonzeroIdeal I (conjAutNormalizedFactor d hI P) =
      conjAutNonzeroIdealMulEquiv (Qsqrtd (d : ℚ))
        (normalizedFactorNonzeroIdeal I P) := by
  apply Subtype.ext
  rfl

/-- The narrow class of a nonzero integral ideal is the product of the narrow
classes of its Dedekind prime factors, counted with multiplicity. -/
theorem narrowClassGroup_mk0_eq_normalizedFactors_prod
    {R : Type*} [CommRing R] [IsDomain R] [IsDedekindDomain R]
    (I : (Ideal R)⁰) :
    NarrowClassGroup.mk0 I =
      ((UniqueFactorizationMonoid.normalizedFactors (I : Ideal R)).attach.map fun P =>
        NarrowClassGroup.mk0 (normalizedFactorNonzeroIdeal I P)).prod := by
  classical
  let s := UniqueFactorizationMonoid.normalizedFactors (I : Ideal R)
  have hI0 : (I : Ideal R) ≠ ⊥ := by
    simpa [Ideal.zero_eq_bot] using mem_nonZeroDivisors_iff_ne_zero.mp I.2
  have hprod : s.prod = (I : Ideal R) :=
    Ideal.prod_normalizedFactors_eq_self hI0
  let F : {P // P ∈ s} → (Ideal R)⁰ := fun P =>
    normalizedFactorNonzeroIdeal I P
  have hFprod : ((s.attach.map F).prod : Ideal R) = (I : Ideal R) := by
    rw [SubmonoidClass.coe_multiset_prod]
    rw [Multiset.map_map]
    change (s.attach.map (fun P : {P // P ∈ s} => (F P : Ideal R))).prod = I
    have hmap :
        s.attach.map (fun P : {P // P ∈ s} => (F P : Ideal R)) = s := by
      change s.attach.map (fun P : {P // P ∈ s} => (P.1 : Ideal R)) = s
      rw [Multiset.attach_map_val]
    rw [hmap]
    exact hprod
  calc
    NarrowClassGroup.mk0 I = NarrowClassGroup.mk0 ((s.attach.map F).prod) := by
      congr 1
      apply Subtype.ext
      exact hFprod.symm
    _ = ((s.attach.map fun P => NarrowClassGroup.mk0 (F P)).prod) := by
      rw [map_multiset_prod]
      rw [Multiset.map_map]
      simp only [Function.comp_apply]
    _ = ((UniqueFactorizationMonoid.normalizedFactors (I : Ideal R)).attach.map fun P =>
        NarrowClassGroup.mk0 (normalizedFactorNonzeroIdeal I P)).prod := rfl

theorem narrowClassGroup_mk0_eq_normalizedFactors_attach_toFinset_prod
    {R : Type*} [CommRing R] [IsDomain R] [IsDedekindDomain R] [DecidableEq (Ideal R)]
    (I : (Ideal R)⁰) :
    NarrowClassGroup.mk0 I =
      ∏ P ∈
          (UniqueFactorizationMonoid.normalizedFactors (I : Ideal R)).attach.toFinset,
        (NarrowClassGroup.mk0 (normalizedFactorNonzeroIdeal I P)) ^
          (UniqueFactorizationMonoid.normalizedFactors (I : Ideal R)).count P.1 := by
  let s := UniqueFactorizationMonoid.normalizedFactors (I : Ideal R)
  let F : {P // P ∈ s} → NarrowClassGroup R := fun P =>
    NarrowClassGroup.mk0 (normalizedFactorNonzeroIdeal I P)
  calc
    NarrowClassGroup.mk0 I = (s.attach.map F).prod := by
      exact narrowClassGroup_mk0_eq_normalizedFactors_prod I
    _ = ∏ P ∈ s.attach.toFinset, F P ^ s.attach.count P := by
      exact Finset.prod_multiset_map_count s.attach F
    _ = ∏ P ∈ s.attach.toFinset, F P ^ s.count P.1 := by
      refine Finset.prod_congr rfl ?_
      intro P _hP
      rw [Multiset.count_attach]

/-- Per-prime contribution in the narrow class group. A split prime factor
cancels with its conjugate, an inert factor is narrowly principal, and a
ramified factor has square one. -/
theorem factor_contribution_by_splitting_narrowClass
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)]
    {I : (Ideal (NumberField.RingOfIntegers (Qsqrtd (d : ℚ))))⁰}
    (hI : IsAmbiguousIdeal (conjAutRingOfIntegers (Qsqrtd (d : ℚ))) I.1)
    (P :
      {P // P ∈ UniqueFactorizationMonoid.normalizedFactors
        (I : Ideal (NumberField.RingOfIntegers (Qsqrtd (d : ℚ))))})
    {p : ℕ} (hp : p.Prime)
    (hcomap : P.1.comap
      (algebraMap ℤ (NumberField.RingOfIntegers (Qsqrtd (d : ℚ)))) = 𝔭(p)) :
    (Ideal.IsSplitIn (𝔭(p)) (NumberField.RingOfIntegers (Qsqrtd (d : ℚ))) ∧
        NarrowClassGroup.mk0 (normalizedFactorNonzeroIdeal I P) *
          NarrowClassGroup.mk0
            (conjAutNonzeroIdealMulEquiv (Qsqrtd (d : ℚ))
              (normalizedFactorNonzeroIdeal I P)) =
          1) ∨
      (Ideal.IsInertIn (𝔭(p)) (NumberField.RingOfIntegers (Qsqrtd (d : ℚ))) ∧
        NarrowClassGroup.mk0 (normalizedFactorNonzeroIdeal I P) = 1) ∨
        (Ideal.IsRamifiedIn (𝔭(p)) (NumberField.RingOfIntegers (Qsqrtd (d : ℚ))) ∧
          (NarrowClassGroup.mk0 (normalizedFactorNonzeroIdeal I P) :
            NarrowClassGroup (NumberField.RingOfIntegers (Qsqrtd (d : ℚ)))) ^ 2 = 1) := by
  let R := NumberField.RingOfIntegers (Qsqrtd (d : ℚ))
  let P0 : (Ideal R)⁰ := normalizedFactorNonzeroIdeal I P
  let σP0 : (Ideal R)⁰ := conjAutNonzeroIdealMulEquiv (Qsqrtd (d : ℚ)) P0
  have hpR_ne : (p : R) ≠ 0 := by
    change algebraMap ℤ R (p : ℤ) ≠ 0
    exact (FaithfulSMul.algebraMap_injective ℤ R).ne (by
      exact_mod_cast hp.ne_zero)
  let spanP0 : (Ideal R)⁰ :=
    ⟨Ideal.span ({(p : R)} : Set R), by
      rw [mem_nonZeroDivisors_iff_ne_zero, Ideal.zero_eq_bot, ne_eq,
        Ideal.span_singleton_eq_bot]
      exact hpR_ne⟩
  have hspanP0_one : NarrowClassGroup.mk0 spanP0 = 1 :=
    narrowClassGroup_mk0_span_singleton_eq_one_of_isTotallyPositive
      hpR_ne (isTotallyPositive_natCast_fractionRing p hp.pos)
  rcases factor_contribution_by_splitting_span d hI P.2 hp hcomap with hsplit | hinert | hram
  · refine Or.inl ⟨hsplit.1, ?_⟩
    calc
      NarrowClassGroup.mk0 (normalizedFactorNonzeroIdeal I P) *
          NarrowClassGroup.mk0
            (conjAutNonzeroIdealMulEquiv (Qsqrtd (d : ℚ))
              (normalizedFactorNonzeroIdeal I P)) =
          NarrowClassGroup.mk0 (P0 * σP0) := by
        simp [P0, σP0, map_mul]
      _ = NarrowClassGroup.mk0 spanP0 := by
        congr 1
        apply Subtype.ext
        exact hsplit.2
      _ = 1 := hspanP0_one
  · refine Or.inr <| Or.inl ⟨hinert.1, ?_⟩
    calc
      NarrowClassGroup.mk0 (normalizedFactorNonzeroIdeal I P) =
          NarrowClassGroup.mk0 spanP0 := by
        congr 1
        apply Subtype.ext
        exact hinert.2
      _ = 1 := hspanP0_one
  · refine Or.inr <| Or.inr ⟨hram.1, ?_⟩
    have hP0_sq : P0 ^ 2 = spanP0 := by
      apply Subtype.ext
      exact hram.2
    calc
      (NarrowClassGroup.mk0 (normalizedFactorNonzeroIdeal I P) :
          NarrowClassGroup R) ^ 2 =
          NarrowClassGroup.mk0 (P0 ^ 2) := by
        simp [P0, map_pow]
      _ = NarrowClassGroup.mk0 spanP0 := by
        rw [hP0_sq]
      _ = 1 := hspanP0_one

theorem split_conj_normalizedFactor_powers_eq_one
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)]
    {I : (Ideal (NumberField.RingOfIntegers (Qsqrtd (d : ℚ))))⁰}
    (hI : IsAmbiguousIdeal (conjAutRingOfIntegers (Qsqrtd (d : ℚ)))
      (I : Ideal (NumberField.RingOfIntegers (Qsqrtd (d : ℚ)))))
    (P :
      {P // P ∈ UniqueFactorizationMonoid.normalizedFactors
        (I : Ideal (NumberField.RingOfIntegers (Qsqrtd (d : ℚ))))})
    {p : ℕ} (hp : p.Prime)
    (hcomap : P.1.comap
      (algebraMap ℤ (NumberField.RingOfIntegers (Qsqrtd (d : ℚ)))) = 𝔭(p))
    (hsplit : Ideal.IsSplitIn (𝔭(p))
      (NumberField.RingOfIntegers (Qsqrtd (d : ℚ)))) :
    (NarrowClassGroup.mk0 (normalizedFactorNonzeroIdeal I P) :
        NarrowClassGroup (NumberField.RingOfIntegers (Qsqrtd (d : ℚ)))) ^
          (UniqueFactorizationMonoid.normalizedFactors
            (I : Ideal (NumberField.RingOfIntegers (Qsqrtd (d : ℚ))))).count P.1 *
      (NarrowClassGroup.mk0
          (normalizedFactorNonzeroIdeal I (conjAutNormalizedFactor d hI P)) :
        NarrowClassGroup (NumberField.RingOfIntegers (Qsqrtd (d : ℚ)))) ^
          (UniqueFactorizationMonoid.normalizedFactors
            (I : Ideal (NumberField.RingOfIntegers (Qsqrtd (d : ℚ))))).count
              (conjAutNormalizedFactor d hI P).1 =
        1 := by
  let R := NumberField.RingOfIntegers (Qsqrtd (d : ℚ))
  let σP := conjAutNormalizedFactor d hI P
  let P0 : (Ideal R)⁰ := normalizedFactorNonzeroIdeal I P
  let σP0 : (Ideal R)⁰ := normalizedFactorNonzeroIdeal I σP
  have hI0 : (I : Ideal R) ≠ ⊥ := by
    simpa [Ideal.zero_eq_bot] using mem_nonZeroDivisors_iff_ne_zero.mp I.2
  have hPprime : P.1.IsPrime := (Ideal.mem_normalizedFactors_iff hI0).mp P.2 |>.1
  have hPover : P.1 ∈ Ideal.primesOver (𝔭(p)) R := ⟨hPprime, ⟨hcomap.symm⟩⟩
  have hpbot : (𝔭(p)) ≠ (⊥ : Ideal ℤ) := by
    rw [Ne, Ideal.span_singleton_eq_bot, Nat.cast_eq_zero]
    exact hp.ne_zero
  haveI : (𝔭(p)).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible
      ((Nat.prime_iff_prime_int.mp hp).irreducible)
  have hσPprime : σP.1.IsPrime := (Ideal.mem_normalizedFactors_iff hI0).mp σP.2 |>.1
  have hσPover : σP.1 ∈ Ideal.primesOver (𝔭(p)) R := by
    refine ⟨hσPprime, ⟨?_⟩⟩
    change 𝔭(p) = σP.1.comap (algebraMap ℤ R)
    rw [conjAutNormalizedFactor_comap_eq d hI P, hcomap]
  have hne : P.1 ≠ σP.1 := by
    have hne' := conjAutNormalizedFactor_ne_of_isSplitIn d hI P hp hcomap hsplit
    intro h
    exact hne' (Subtype.ext h.symm)
  have hmap :
      Ideal.map (algebraMap ℤ R) (𝔭(p)) = P.1 * σP.1 :=
    map_eq_mul_of_isSplitIn_of_mem_primesOver_of_ne
      (S := R) (p := 𝔭(p)) (by simp [ringChar.eq_zero]) hpbot
      hPover hσPover hne hsplit
  have hmapSpan :
      Ideal.map (algebraMap ℤ R) (𝔭(p)) =
        Ideal.span ({(p : R)} : Set R) := by
    rw [Ideal.map_span, Set.image_singleton]
    rfl
  have hpR_ne : (p : R) ≠ 0 := by
    change algebraMap ℤ R (p : ℤ) ≠ 0
    exact (FaithfulSMul.algebraMap_injective ℤ R).ne (by
      exact_mod_cast hp.ne_zero)
  let spanP0 : (Ideal R)⁰ :=
    ⟨Ideal.span ({(p : R)} : Set R), by
      rw [mem_nonZeroDivisors_iff_ne_zero, Ideal.zero_eq_bot, ne_eq,
        Ideal.span_singleton_eq_bot]
      exact hpR_ne⟩
  have hspanP0_one : NarrowClassGroup.mk0 spanP0 = 1 :=
    narrowClassGroup_mk0_span_singleton_eq_one_of_isTotallyPositive
      hpR_ne (isTotallyPositive_natCast_fractionRing p hp.pos)
  have hPσP : P0 * σP0 = spanP0 := by
    apply Subtype.ext
    exact hmap.symm.trans hmapSpan
  have hpair_one :
      NarrowClassGroup.mk0 P0 * NarrowClassGroup.mk0 σP0 =
        (1 : NarrowClassGroup R) := by
    calc
      NarrowClassGroup.mk0 P0 * NarrowClassGroup.mk0 σP0 =
          NarrowClassGroup.mk0 (P0 * σP0) := by
        rw [map_mul]
      _ = NarrowClassGroup.mk0 spanP0 := by rw [hPσP]
      _ = 1 := hspanP0_one
  have hcount :
      (UniqueFactorizationMonoid.normalizedFactors (I : Ideal R)).count σP.1 =
        (UniqueFactorizationMonoid.normalizedFactors (I : Ideal R)).count P.1 :=
    normalizedFactors_count_conjAutNormalizedFactor_eq d hI P
  change
    (NarrowClassGroup.mk0 P0 : NarrowClassGroup R) ^
          (UniqueFactorizationMonoid.normalizedFactors (I : Ideal R)).count P.1 *
      (NarrowClassGroup.mk0 σP0 : NarrowClassGroup R) ^
          (UniqueFactorizationMonoid.normalizedFactors (I : Ideal R)).count σP.1 =
        1
  rw [hcount, ← mul_pow, hpair_one, one_pow]

theorem inert_normalizedFactor_power_eq_one
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)]
    {I : (Ideal (NumberField.RingOfIntegers (Qsqrtd (d : ℚ))))⁰}
    (P :
      {P // P ∈ UniqueFactorizationMonoid.normalizedFactors
        (I : Ideal (NumberField.RingOfIntegers (Qsqrtd (d : ℚ))))})
    {p : ℕ} (hp : p.Prime)
    (hcomap : P.1.comap
      (algebraMap ℤ (NumberField.RingOfIntegers (Qsqrtd (d : ℚ)))) = 𝔭(p))
    (hinert : Ideal.IsInertIn (𝔭(p))
      (NumberField.RingOfIntegers (Qsqrtd (d : ℚ)))) :
    (NarrowClassGroup.mk0 (normalizedFactorNonzeroIdeal I P) :
        NarrowClassGroup (NumberField.RingOfIntegers (Qsqrtd (d : ℚ)))) ^
          (UniqueFactorizationMonoid.normalizedFactors
            (I : Ideal (NumberField.RingOfIntegers (Qsqrtd (d : ℚ))))).count P.1 =
        1 := by
  let R := NumberField.RingOfIntegers (Qsqrtd (d : ℚ))
  let P0 : (Ideal R)⁰ := normalizedFactorNonzeroIdeal I P
  have hI0 : (I : Ideal R) ≠ ⊥ := by
    simpa [Ideal.zero_eq_bot] using mem_nonZeroDivisors_iff_ne_zero.mp I.2
  have hPprime : P.1.IsPrime := (Ideal.mem_normalizedFactors_iff hI0).mp P.2 |>.1
  have hmap :=
    map_span_eq_of_isInertIn_of_comap_eq_p (d := d) hPprime hp hcomap hinert
  have hmapSpan :
      Ideal.map (algebraMap ℤ R) (𝔭(p)) =
        Ideal.span ({(p : R)} : Set R) := by
    rw [Ideal.map_span, Set.image_singleton]
    rfl
  have hpR_ne : (p : R) ≠ 0 := by
    change algebraMap ℤ R (p : ℤ) ≠ 0
    exact (FaithfulSMul.algebraMap_injective ℤ R).ne (by
      exact_mod_cast hp.ne_zero)
  let spanP0 : (Ideal R)⁰ :=
    ⟨Ideal.span ({(p : R)} : Set R), by
      rw [mem_nonZeroDivisors_iff_ne_zero, Ideal.zero_eq_bot, ne_eq,
        Ideal.span_singleton_eq_bot]
      exact hpR_ne⟩
  have hP0 : P0 = spanP0 := by
    apply Subtype.ext
    exact hmap.symm.trans hmapSpan
  have hmk : NarrowClassGroup.mk0 P0 = (1 : NarrowClassGroup R) := by
    rw [hP0]
    exact narrowClassGroup_mk0_span_singleton_eq_one_of_isTotallyPositive
      hpR_ne (isTotallyPositive_natCast_fractionRing p hp.pos)
  change
    (NarrowClassGroup.mk0 P0 : NarrowClassGroup R) ^
          (UniqueFactorizationMonoid.normalizedFactors (I : Ideal R)).count P.1 =
        1
  rw [hmk, one_pow]

theorem normalizedFactors_nonramified_count_prod_eq_one_of_isAmbiguousIdeal
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)]
    (J : (Ideal (NumberField.RingOfIntegers (Qsqrtd (d : ℚ))))⁰)
    (hJ : IsAmbiguousIdeal (conjAutRingOfIntegers (Qsqrtd (d : ℚ)))
      (J : Ideal (NumberField.RingOfIntegers (Qsqrtd (d : ℚ)))))
    [DecidablePred (fun P :
        {P // P ∈ UniqueFactorizationMonoid.normalizedFactors
          (J : Ideal (NumberField.RingOfIntegers (Qsqrtd (d : ℚ))))} =>
      ¬ normalizedFactorIsRamified d P)] :
    (∏ P ∈
        (UniqueFactorizationMonoid.normalizedFactors
          (J : Ideal (NumberField.RingOfIntegers (Qsqrtd (d : ℚ))))).attach.toFinset with
        ¬ normalizedFactorIsRamified d P,
      (NarrowClassGroup.mk0 (normalizedFactorNonzeroIdeal J P) :
        NarrowClassGroup (NumberField.RingOfIntegers (Qsqrtd (d : ℚ)))) ^
        (UniqueFactorizationMonoid.normalizedFactors
          (J : Ideal (NumberField.RingOfIntegers (Qsqrtd (d : ℚ))))).count P.1) =
      1 := by
  classical
  let R := NumberField.RingOfIntegers (Qsqrtd (d : ℚ))
  let s := UniqueFactorizationMonoid.normalizedFactors (J : Ideal R)
  let S := s.attach.toFinset
  let f : {P // P ∈ s} → NarrowClassGroup R := fun P =>
    (NarrowClassGroup.mk0 (normalizedFactorNonzeroIdeal J P) :
        NarrowClassGroup R) ^ s.count P.1
  let σ : {P // P ∈ s} → {P // P ∈ s} := conjAutNormalizedFactor d hJ
  change (∏ P ∈ S with ¬ normalizedFactorIsRamified d P, f P) = 1
  refine Finset.prod_involution
    (s := S.filter fun P => ¬ normalizedFactorIsRamified d P)
    (f := f) (g := fun P _hP => σ P) ?_ ?_ ?_ ?_
  · intro P hP
    have hPnonram : ¬ normalizedFactorIsRamified d P := (Finset.mem_filter.mp hP).2
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
    · simpa [f, σ, s, R] using
        split_conj_normalizedFactor_powers_eq_one d hJ P hp hcomap hsplit.1
    · have hP_one : f P = 1 := by
        simpa [f, s, R] using inert_normalizedFactor_power_eq_one d P hp hcomap hinert.1
      have hσcomap : (σ P).1.comap (algebraMap ℤ R) = 𝔭(p) := by
        simpa [σ, R] using
          (conjAutNormalizedFactor_comap_eq d hJ P).trans hcomap
      have hσ_one : f (σ P) = 1 := by
        simpa [f, σ, s, R] using
          inert_normalizedFactor_power_eq_one d (conjAutNormalizedFactor d hJ P)
            hp hσcomap hinert.1
      rw [hP_one, hσ_one, one_mul]
    · exact False.elim (hPnonram ⟨p, hp, hcomap, hram.1⟩)
  · intro P hP hfP
    have hPnonram : ¬ normalizedFactorIsRamified d P := (Finset.mem_filter.mp hP).2
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
    · exact conjAutNormalizedFactor_ne_of_isSplitIn d hJ P hp hcomap hsplit.1
    · exact False.elim <| hfP <| by
        simpa [f, s, R] using inert_normalizedFactor_power_eq_one d P hp hcomap hinert.1
    · exact False.elim (hPnonram ⟨p, hp, hcomap, hram.1⟩)
  · intro P hP
    rw [Finset.mem_filter]
    refine ⟨by simp [S, σ], ?_⟩
    have hPnonram : ¬ normalizedFactorIsRamified d P := (Finset.mem_filter.mp hP).2
    intro hσram
    exact hPnonram ((normalizedFactorIsRamified_conjAutNormalizedFactor_iff d hJ P).mp hσram)
  · intro P _hP
    exact conjAutNormalizedFactor_involutive d hJ P

theorem normalizedFactors_ramified_count_prod_eq_ramifiedPrime_count_prod
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
  let term : {p // p ∈ ramifiedPrimes d} → NarrowClassGroup R := fun p =>
    (ramifiedPrimeNarrowClass d p.2) ^ s.count (ramifiedPrimeIdeal d p.2)
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
      have hPram : normalizedFactorIsRamified d P := (Finset.mem_filter.mp hP).2
      let p := ramifiedPrimeOfNormalizedFactor d P hPram
      have hP_eq :
          P.1 = ramifiedPrimeIdeal d p.2 :=
        normalizedFactor_eq_ramifiedPrimeIdeal_ramifiedPrimeOfNormalizedFactor d P hPram
      have hmk :
          NarrowClassGroup.mk0 (normalizedFactorNonzeroIdeal J P) =
            ramifiedPrimeNarrowClass d p.2 := by
        rw [ramifiedPrimeNarrowClass]
        congr 1
        apply Subtype.ext
        exact hP_eq
      dsimp [f, term, p]
      rw [hmk, hP_eq]
  have hright :
      (∏ p ∈ T, term p) =
        Finset.univ.prod fun p : {p // p ∈ ramifiedPrimes d} =>
          (ramifiedPrimeNarrowClass d p.2) ^
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
  exact hleft.trans hright

/-- Quadratic conjugation acts on the narrow ideal class group by inversion. The
point not present in the ordinary class-group statement is positivity: the
principal generator of `I * σ(I)` is the positive integer `absNorm I`. -/
theorem narrowClassGroup_mk0_map_conjAut_eq_inv
    (K : Type*) [Field K] [NumberField K] [Algebra ℚ K]
    [QuadraticField K] [QuadraticField.Conj K]
    (I : (Ideal (NumberField.RingOfIntegers K))⁰) :
    NarrowClassGroup.mk0 (conjAutNonzeroIdealMulEquiv K I) =
      (NarrowClassGroup.mk0 I)⁻¹ := by
  let R := NumberField.RingOfIntegers K
  have hI0 : (I : Ideal R) ≠ ⊥ := by
    simpa [Ideal.zero_eq_bot] using mem_nonZeroDivisors_iff_ne_zero.mp I.2
  have hnorm0 : Ideal.absNorm (I : Ideal R) ≠ 0 :=
    mt Ideal.absNorm_eq_zero_iff.mp hI0
  have hnormR_ne : (Ideal.absNorm (I : Ideal R) : R) ≠ 0 := by
    change algebraMap ℕ R (Ideal.absNorm (I : Ideal R)) ≠ 0
    simpa using (FaithfulSMul.algebraMap_injective ℕ R).ne hnorm0
  have hprod :
      NarrowClassGroup.mk0 I *
          NarrowClassGroup.mk0 (conjAutNonzeroIdealMulEquiv K I) =
        1 := by
    calc
      NarrowClassGroup.mk0 I *
          NarrowClassGroup.mk0 (conjAutNonzeroIdealMulEquiv K I) =
          NarrowClassGroup.mk0 (I * conjAutNonzeroIdealMulEquiv K I) := by
        rw [map_mul]
      _ =
          NarrowClassGroup.mk0
            (R := R)
            ⟨Ideal.span ({(Ideal.absNorm (I : Ideal R) : R)} : Set R), by
              rw [mem_nonZeroDivisors_iff_ne_zero, Ideal.zero_eq_bot, ne_eq,
                Ideal.span_singleton_eq_bot]
              exact hnormR_ne⟩ := by
        congr 1
        apply Subtype.ext
        simpa [R] using mul_map_conjAut_eq_span_absNorm K (I : Ideal R)
      _ = 1 :=
        narrowClassGroup_mk0_span_singleton_eq_one_of_isTotallyPositive
          hnormR_ne
          (isTotallyPositive_natCast_fractionRing
            (Ideal.absNorm (I : Ideal R)) (Nat.pos_of_ne_zero hnorm0))
  exact eq_inv_of_mul_eq_one_right hprod

theorem narrowClassGroup_mk0_sq_eq_one_ramifiedPrimeIdeal
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)]
    {p : ℕ} (hp : p ∈ ramifiedPrimes d) :
    (ramifiedPrimeNarrowClass d hp :
        NarrowClassGroup (NumberField.RingOfIntegers (Qsqrtd (d : ℚ)))) ^ 2 = 1 := by
  let R := NumberField.RingOfIntegers (Qsqrtd (d : ℚ))
  have hpPrime : p.Prime := prime_of_mem_ramifiedPrimes hp
  have hram :
      Ideal.IsRamifiedIn (𝔭(p)) R :=
    ((mem_ramifiedPrimes_iff_isRamifiedIn d p).mp hp).2
  let P0 : (Ideal R)⁰ :=
    ⟨ramifiedPrimeIdeal d hp,
      mem_nonZeroDivisors_iff_ne_zero.mpr (by
        simpa [Ideal.zero_eq_bot] using ramifiedPrimeIdeal_ne_bot d hp)⟩
  have hP0 :
      ramifiedPrimeNarrowClass d hp = NarrowClassGroup.mk0 P0 := by
    rfl
  have hmap :
      Ideal.map (algebraMap ℤ R) (𝔭(p)) = (ramifiedPrimeIdeal d hp) ^ 2 := by
    exact map_span_eq_sq_of_isRamifiedIn_of_mem_primesOver (d := d) hpPrime
      (ramifiedPrimeIdeal_mem_primesOver d hp) hram
  have hspan :
      Ideal.map (algebraMap ℤ R) (𝔭(p)) = Ideal.span ({(p : R)} : Set R) := by
    rw [Ideal.map_span, Set.image_singleton]
    rfl
  have hpR_ne : (p : R) ≠ 0 := by
    change algebraMap ℤ R (p : ℤ) ≠ 0
    exact (FaithfulSMul.algebraMap_injective ℤ R).ne (by
      exact_mod_cast hpPrime.ne_zero)
  have hP0_sq :
      (P0 ^ 2 : (Ideal R)⁰) =
        ⟨Ideal.span ({(p : R)} : Set R), by
          rw [mem_nonZeroDivisors_iff_ne_zero, Ideal.zero_eq_bot, ne_eq,
            Ideal.span_singleton_eq_bot]
          exact hpR_ne⟩ := by
    apply Subtype.ext
    exact hmap.symm.trans hspan
  rw [hP0, pow_two, ← map_mul, ← pow_two, hP0_sq]
  exact narrowClassGroup_mk0_span_singleton_eq_one_of_isTotallyPositive
    hpR_ne
    (isTotallyPositive_natCast_fractionRing p hpPrime.pos)

noncomputable def ramifiedParityClassProduct
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)]
    {p0 : ℕ} (_hp0 : p0 ∈ ramifiedPrimes d)
    (v : ({p // p ∈ (ramifiedPrimes d).erase p0} → Fin 2)) :
    ClassGroup (NumberField.RingOfIntegers (Qsqrtd (d : ℚ))) :=
  Finset.univ.prod fun p : {p // p ∈ (ramifiedPrimes d).erase p0} =>
    if v p = 0 then 1 else
      ClassGroup.mk0
        (⟨ramifiedPrimeIdeal d ((Finset.mem_erase.mp p.2).2),
          mem_nonZeroDivisors_iff_ne_zero.mpr (by
            simpa [Ideal.zero_eq_bot] using
              ramifiedPrimeIdeal_ne_bot d ((Finset.mem_erase.mp p.2).2))⟩ :
          (Ideal (NumberField.RingOfIntegers (Qsqrtd (d : ℚ))))⁰)

theorem ramifiedParityClassProduct_sq_eq_one
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)]
    {p0 : ℕ} (hp0 : p0 ∈ ramifiedPrimes d)
    (v : ({p // p ∈ (ramifiedPrimes d).erase p0} → Fin 2)) :
    (ramifiedParityClassProduct d hp0 v :
      ClassGroup (NumberField.RingOfIntegers (Qsqrtd (d : ℚ)))) ^ 2 = 1 := by
  classical
  rw [ramifiedParityClassProduct, ← Finset.prod_pow]
  refine Finset.prod_eq_one ?_
  intro p _hp
  by_cases hpv : v p = 0
  · simp [hpv]
  · simp [hpv, classGroup_mk0_sq_eq_one_ramifiedPrimeIdeal]

noncomputable def ramifiedParityNarrowClassProduct
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)]
    {p0 : ℕ} (_hp0 : p0 ∈ ramifiedPrimes d)
    (v : ({p // p ∈ (ramifiedPrimes d).erase p0} → Fin 2)) :
    NarrowClassGroup (NumberField.RingOfIntegers (Qsqrtd (d : ℚ))) := by
  classical
  exact Finset.univ.prod fun p =>
    if v p = 0 then 1 else
      ramifiedPrimeNarrowClass d ((Finset.mem_erase.mp p.2).2)

noncomputable def fullRamifiedParityNarrowClassProduct
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)]
    (v : ({p // p ∈ ramifiedPrimes d} → Fin 2)) :
    NarrowClassGroup (NumberField.RingOfIntegers (Qsqrtd (d : ℚ))) := by
  classical
  exact Finset.univ.prod fun p =>
    if v p = 0 then 1 else ramifiedPrimeNarrowClass d p.2

theorem mk0_ramifiedParityIdealProduct
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)]
    {p0 : ℕ} (hp0 : p0 ∈ ramifiedPrimes d)
    (v : ({p // p ∈ (ramifiedPrimes d).erase p0} → Fin 2)) :
    NarrowClassGroup.mk0 (ramifiedParityIdealProduct d hp0 v) =
      ramifiedParityNarrowClassProduct d hp0 v := by
  classical
  rw [ramifiedParityIdealProduct, ramifiedParityNarrowClassProduct]
  simp only [map_prod]
  refine Finset.prod_congr rfl ?_
  intro p _hp
  by_cases hpv : v p = 0
  · simp [hpv]
  · simp [hpv, ramifiedPrimeNarrowClass]

theorem mk0_fullRamifiedParityIdealProduct
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)]
    (v : ({p // p ∈ ramifiedPrimes d} → Fin 2)) :
    NarrowClassGroup.mk0 (fullRamifiedParityIdealProduct d v) =
      fullRamifiedParityNarrowClassProduct d v := by
  classical
  rw [fullRamifiedParityIdealProduct, fullRamifiedParityNarrowClassProduct]
  simp only [map_prod]
  refine Finset.prod_congr rfl ?_
  intro p _hp
  by_cases hpv : v p = 0
  · simp [hpv]
  · simp [hpv, ramifiedPrimeNarrowClass]

theorem toClassGroup_ramifiedParityNarrowClassProduct
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)]
    {p0 : ℕ} (hp0 : p0 ∈ ramifiedPrimes d)
    (v : ({p // p ∈ (ramifiedPrimes d).erase p0} → Fin 2)) :
    NarrowClassGroup.toClassGroup (NumberField.RingOfIntegers (Qsqrtd (d : ℚ)))
        (ramifiedParityNarrowClassProduct d hp0 v) =
      ramifiedParityClassProduct d hp0 v := by
  classical
  rw [ramifiedParityNarrowClassProduct, ramifiedParityClassProduct]
  simp only [map_prod]
  refine Finset.prod_congr rfl ?_
  intro p _hp
  by_cases hpv : v p = 0
  · simp [hpv]
  · simp [hpv, toClassGroup_ramifiedPrimeNarrowClass]

theorem ramifiedParityNarrowClassProduct_sq_eq_one
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)]
    {p0 : ℕ} (hp0 : p0 ∈ ramifiedPrimes d)
    (v : ({p // p ∈ (ramifiedPrimes d).erase p0} → Fin 2)) :
    (ramifiedParityNarrowClassProduct d hp0 v :
      NarrowClassGroup (NumberField.RingOfIntegers (Qsqrtd (d : ℚ)))) ^ 2 = 1 := by
  classical
  rw [ramifiedParityNarrowClassProduct, ← Finset.prod_pow]
  refine Finset.prod_eq_one ?_
  intro p _hp
  by_cases hpv : v p = 0
  · simp [hpv]
  · simp [hpv, narrowClassGroup_mk0_sq_eq_one_ramifiedPrimeIdeal]

theorem fullRamifiedParityNarrowClassProduct_sq_eq_one
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)]
    (v : ({p // p ∈ ramifiedPrimes d} → Fin 2)) :
    (fullRamifiedParityNarrowClassProduct d v :
      NarrowClassGroup (NumberField.RingOfIntegers (Qsqrtd (d : ℚ)))) ^ 2 = 1 := by
  classical
  rw [fullRamifiedParityNarrowClassProduct, ← Finset.prod_pow]
  refine Finset.prod_eq_one ?_
  intro p _hp
  by_cases hpv : v p = 0
  · simp [hpv]
  · simp [hpv, narrowClassGroup_mk0_sq_eq_one_ramifiedPrimeIdeal]

/-- Indicator products for `Fin 2` add in any group where the indicated element
has order dividing two. -/
theorem fin_two_indicator_mul_indicator {G : Type*} [Group G] {a : G}
    (ha : a ^ 2 = 1) (x y : Fin 2) :
    (if x + y = 0 then 1 else a) = (if x = 0 then 1 else a) *
      (if y = 0 then 1 else a) := by
  fin_cases x <;> fin_cases y
  · simp
  · simp
  · simp
  · simpa [pow_two] using ha.symm

/-- The full ramified parity narrow-class product is additive in its
`Fin 2`-valued parity vector. -/
theorem fullRamifiedParityNarrowClassProduct_add
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)]
    (v r : ({p // p ∈ ramifiedPrimes d} → Fin 2)) :
    fullRamifiedParityNarrowClassProduct d (fun p => v p + r p) =
      fullRamifiedParityNarrowClassProduct d v * fullRamifiedParityNarrowClassProduct d r := by
  classical
  rw [fullRamifiedParityNarrowClassProduct, fullRamifiedParityNarrowClassProduct,
    fullRamifiedParityNarrowClassProduct]
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl ?_
  intro p _hp
  exact fin_two_indicator_mul_indicator
    (narrowClassGroup_mk0_sq_eq_one_ramifiedPrimeIdeal d p.2) (v p) (r p)

/-- The zero full ramified parity vector maps to the trivial narrow class. -/
theorem fullRamifiedParityNarrowClassProduct_zero
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] :
    fullRamifiedParityNarrowClassProduct d 0 = 1 := by
  simp [fullRamifiedParityNarrowClassProduct]

/-- The full ramified parity product, bundled as a homomorphism from the additive
`Fin 2` parity-vector group to the narrow class group. -/
noncomputable def fullRamifiedParityNarrowClassHom
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] :
    Multiplicative ({p // p ∈ ramifiedPrimes d} → Fin 2) →*
      NarrowClassGroup (NumberField.RingOfIntegers (Qsqrtd (d : ℚ))) where
  toFun v := fullRamifiedParityNarrowClassProduct d (Multiplicative.toAdd v)
  map_one' := by
    simpa using fullRamifiedParityNarrowClassProduct_zero d
  map_mul' v r := by
    change
      fullRamifiedParityNarrowClassProduct d
          (fun p => Multiplicative.toAdd v p + Multiplicative.toAdd r p) =
        fullRamifiedParityNarrowClassProduct d (Multiplicative.toAdd v) *
          fullRamifiedParityNarrowClassProduct d (Multiplicative.toAdd r)
    exact fullRamifiedParityNarrowClassProduct_add d
      (Multiplicative.toAdd v) (Multiplicative.toAdd r)

theorem fullRamifiedParityNarrowClassHom_apply
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)]
    (v : {p // p ∈ ramifiedPrimes d} → Fin 2) :
    fullRamifiedParityNarrowClassHom d (Multiplicative.ofAdd v) =
      fullRamifiedParityNarrowClassProduct d v :=
  rfl

theorem fullRamifiedParityNarrowClassHom_mem_ker_iff
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)]
    (v : {p // p ∈ ramifiedPrimes d} → Fin 2) :
    Multiplicative.ofAdd v ∈ (fullRamifiedParityNarrowClassHom d).ker ↔
      fullRamifiedParityNarrowClassProduct d v = 1 := by
  simp [MonoidHom.mem_ker, fullRamifiedParityNarrowClassHom_apply]

theorem multiplicative_ofAdd_ne_one_of_exists_apply_ne_zero
    {ι : Type*} (v : ι → Fin 2) (hv : ∃ i, v i ≠ 0) :
    Multiplicative.ofAdd v ≠ 1 := by
  rintro h
  obtain ⟨i, hi⟩ := hv
  have hv0 : v = 0 := by
    simpa using congrArg Multiplicative.toAdd h
  exact hi (by simp [hv0])

theorem exists_apply_ne_zero_of_multiplicative_ne_one
    {ι : Type*} (v : Multiplicative (ι → Fin 2)) (hv : v ≠ 1) :
    ∃ i, Multiplicative.toAdd v i ≠ 0 := by
  by_contra h
  apply hv
  apply Multiplicative.toAdd.injective
  funext i
  by_contra hi
  exact h ⟨i, hi⟩

/-- The weak positive-principal relation is equivalent to a nontrivial kernel
element for the full ramified parity homomorphism. -/
theorem exists_nonzero_fullRamifiedParityNarrowClassProduct_eq_one_iff
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] :
    (∃ r : ({p // p ∈ ramifiedPrimes d} → Fin 2),
      (∃ p, r p ≠ 0) ∧ fullRamifiedParityNarrowClassProduct d r = 1) ↔
    ∃ r : Multiplicative ({p // p ∈ ramifiedPrimes d} → Fin 2),
      r ≠ 1 ∧ r ∈ (fullRamifiedParityNarrowClassHom d).ker := by
  constructor
  · rintro ⟨r, hrnonzero, hr⟩
    refine ⟨Multiplicative.ofAdd r, ?_, ?_⟩
    · exact multiplicative_ofAdd_ne_one_of_exists_apply_ne_zero r hrnonzero
    · exact (fullRamifiedParityNarrowClassHom_mem_ker_iff d r).mpr hr
  · rintro ⟨r, hrne, hrker⟩
    let v : {p // p ∈ ramifiedPrimes d} → Fin 2 := Multiplicative.toAdd r
    refine ⟨v, ?_, ?_⟩
    · exact exists_apply_ne_zero_of_multiplicative_ne_one r hrne
    · exact (fullRamifiedParityNarrowClassHom_mem_ker_iff d v).mp hrker

/-- After erasing one ramified rational prime, the remaining `Fin 2` parity
vectors have cardinality `2 ^ (t - 1)`. -/
theorem card_erasedRamifiedParityVectorDomain
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)]
    {p0 : ℕ} (hp0 : p0 ∈ ramifiedPrimes d) :
    Nat.card ({p // p ∈ (ramifiedPrimes d).erase p0} → Fin 2) =
      2 ^ (ramifiedPrimeCount d - 1) := by
  rw [Nat.card_fun, Nat.card_fin, Nat.card_eq_finsetCard, Finset.card_erase_of_mem hp0,
    ← ramifiedPrimeCount_eq_card]

theorem ramifiedPrimeNarrowClass_pow_normalizedFactors_count_eq_parity
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)]
    (J : (Ideal (NumberField.RingOfIntegers (Qsqrtd (d : ℚ))))⁰)
    (p : {p // p ∈ ramifiedPrimes d}) :
    (ramifiedPrimeNarrowClass d p.2) ^
        (UniqueFactorizationMonoid.normalizedFactors
          (J : Ideal (NumberField.RingOfIntegers (Qsqrtd (d : ℚ))))).count
            (ramifiedPrimeIdeal d p.2) =
      if fullRamifiedParityVector d J p = 0 then 1 else ramifiedPrimeNarrowClass d p.2 := by
  let n :=
    (UniqueFactorizationMonoid.normalizedFactors
      (J : Ideal (NumberField.RingOfIntegers (Qsqrtd (d : ℚ))))).count
        (ramifiedPrimeIdeal d p.2)
  let a := ramifiedPrimeNarrowClass d p.2
  have ha2 : a ^ 2 = 1 := by
    simpa [a] using narrowClassGroup_mk0_sq_eq_one_ramifiedPrimeIdeal d p.2
  have hpow : a ^ n = a ^ (n % 2) :=
    pow_eq_pow_of_modEq (Nat.mod_modEq n 2).symm ha2
  by_cases hpv : fullRamifiedParityVector d J p = 0
  · have hnmod : n % 2 = 0 := by
      have hval := congrArg Fin.val hpv
      simpa [fullRamifiedParityVector, n] using hval
    rw [if_pos hpv]
    calc
      a ^ n = a ^ (n % 2) := hpow
      _ = 1 := by rw [hnmod, pow_zero]
  · have hpv_one : fullRamifiedParityVector d J p = 1 :=
      Fin.eq_one_of_ne_zero (fullRamifiedParityVector d J p) hpv
    have hnmod : n % 2 = 1 := by
      have hval := congrArg Fin.val hpv_one
      simpa [fullRamifiedParityVector, n] using hval
    rw [if_neg hpv]
    calc
      a ^ n = a ^ (n % 2) := hpow
      _ = a := by rw [hnmod, pow_one]

theorem fullRamifiedParityNarrowClassProduct_eq_ramifiedPrime_count_prod
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)]
    (J : (Ideal (NumberField.RingOfIntegers (Qsqrtd (d : ℚ))))⁰) :
    fullRamifiedParityNarrowClassProduct d (fullRamifiedParityVector d J) =
      Finset.univ.prod fun p : {p // p ∈ ramifiedPrimes d} =>
        (ramifiedPrimeNarrowClass d p.2) ^
          (UniqueFactorizationMonoid.normalizedFactors
            (J : Ideal (NumberField.RingOfIntegers (Qsqrtd (d : ℚ))))).count
            (ramifiedPrimeIdeal d p.2) := by
  classical
  rw [fullRamifiedParityNarrowClassProduct]
  refine Finset.prod_congr rfl ?_
  intro p _hp
  exact (ramifiedPrimeNarrowClass_pow_normalizedFactors_count_eq_parity d J p).symm

theorem narrowClassGroup_mk0_sq_eq_one_ramifiedParityIdealProduct
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)]
    {p0 : ℕ} (hp0 : p0 ∈ ramifiedPrimes d)
    (v : ({p // p ∈ (ramifiedPrimes d).erase p0} → Fin 2)) :
    (NarrowClassGroup.mk0 (ramifiedParityIdealProduct d hp0 v) :
        NarrowClassGroup (NumberField.RingOfIntegers (Qsqrtd (d : ℚ)))) ^ 2 = 1 := by
  rw [mk0_ramifiedParityIdealProduct d hp0 v]
  exact ramifiedParityNarrowClassProduct_sq_eq_one d hp0 v

/-- Narrow ideal classes fixed by inversion. For quadratic fields, this is the
group-theoretic target that will be identified with conjugation-fixed classes. -/
def NarrowInversionFixedClass (R : Type*) [CommRing R] [IsDomain R] :=
  {C : NarrowClassGroup R // C = C⁻¹}

/-- The two-torsion subgroup of the narrow class group is equivalent to the
subtype of narrow ideal classes fixed by inversion. -/
def narrowTwoTorsionEquivInversionFixedClass
    (R : Type*) [CommRing R] [IsDomain R] :
    NarrowClassGroup.twoTorsion R ≃ NarrowInversionFixedClass R where
  toFun C := by
    refine ⟨(C : NarrowClassGroup R), ?_⟩
    have hpow : (C : NarrowClassGroup R) ^ 2 = 1 := by
      simpa using (NarrowClassGroup.mem_twoTorsion_iff R C).mp C.2
    have hmul : (C : NarrowClassGroup R) * C = 1 := by
      simpa [pow_two] using hpow
    exact (eq_inv_iff_mul_eq_one).2 hmul
  invFun C := by
    refine ⟨C.1, ?_⟩
    rw [NarrowClassGroup.mem_twoTorsion_iff]
    have hmul : (C.1 : NarrowClassGroup R) * C.1 = 1 := by
      nth_rewrite 1 [C.2]
      rw [inv_mul_cancel]
    simpa [pow_two] using hmul
  left_inv C := by
    ext
    rfl
  right_inv C := by
    apply Subtype.ext
    rfl

/-- Counting `Cl⁺[2]` is the same as counting inversion-fixed narrow ideal
classes. -/
theorem card_narrowClassGroupTwoTorsion_eq_card_narrowInversionFixedClass
    (R : Type*) [CommRing R] [IsDomain R] :
    Nat.card (NarrowClassGroup.twoTorsion R) =
      Nat.card (NarrowInversionFixedClass R) :=
  Nat.card_congr (narrowTwoTorsionEquivInversionFixedClass R)

end Internal
end GenusTheory
end ClassGroup
end QuadraticNumberFields
