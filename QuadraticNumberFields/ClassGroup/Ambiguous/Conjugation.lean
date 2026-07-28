/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/

import Mathlib.RingTheory.Ideal.Norm.RelNorm
import QNFMathlib.RingTheory.Ideal.RingEquiv
import QuadraticNumberFields.ClassGroup.Ambiguous.Ramified
import QuadraticNumberFields.RingOfIntegers.Conj
import QuadraticNumberFields.Splitting.Galois

/-!
# Conjugation on ideal classes

Let `K` be a quadratic field, and let `σ` be its nontrivial conjugation. We use
conjugation on ideals, ideal factorizations, and ideal classes.

For a nonzero integral ideal `I`,

`I * σ(I) = (Norm I)`

after mapping the norm from `ℤ` to `𝓞 K`. In the ordinary and narrow class groups this
gives

`[σ(I)] = [I]⁻¹`,        `[σ(I)]⁺ = [I]⁺⁻¹`.

For a rational prime `p` and a prime ideal `P ∣ p`, conjugation keeps `P` above
`p`. It fixes `P` in the ramified and inert cases, and swaps the two primes
above `p` in the split case. This gives the ramified-prime contribution to
ambiguous narrow classes.

In particular, a narrow class fixed by conjugation satisfies

`[I]⁺ = [I]⁺⁻¹`,

so it is 2-torsion.
-/

namespace QuadraticNumberFields
namespace ClassGroup
namespace Ambiguous

open scoped nonZeroDivisors NumberField Pointwise
open scoped QuadraticNumberFields.Splitting

attribute [-instance] DivisionRing.toRatAlgebra
attribute [local instance] FractionRing.liftAlgebra

private theorem ringChar_int_ne_two : ringChar ℤ ≠ 2 := by
  simp [ringChar.eq_zero]

private theorem map_pIdeal_eq_span_natCast
    (R : Type*) [CommRing R] [Algebra ℤ R] (p : ℕ) :
    Ideal.map (algebraMap ℤ R) (𝔭(p)) = Ideal.span ({(p : R)} : Set R) := by
  rw [Ideal.map_span, Set.image_singleton]
  simp

private theorem nonzeroIdeal_ne_bot {R : Type*} [CommRing R] [IsDedekindDomain R]
    (I : (Ideal R)⁰) :
    (I : Ideal R) ≠ ⊥ := by
  simpa [Ideal.zero_eq_bot] using nonZeroDivisors.coe_ne_zero I

section ConjugationIdealFactors

variable (K : Type*) [Field K] [Algebra ℚ K] [QuadraticField K] [QuadraticField.Conj K]

local notation "OK" => NumberField.RingOfIntegers K

/-- The conjugate of a nonzero ideal is nonzero, since conjugation is bijective. -/
theorem map_conjAut_mem_nonZeroDivisors {I : Ideal OK}
    (hI : I ∈ nonZeroDivisors (Ideal OK)) :
    Ideal.map (conjAutRingOfIntegers K : OK →+* OK) I ∈
      nonZeroDivisors (Ideal OK) :=
  Ideal.map_ringEquiv_mem_nonZeroDivisors (conjAutRingOfIntegers K) hI

/-- For an ambiguous nonzero ideal, conjugation preserves normalized-factor
multiplicity. -/
theorem map_conjAut_count_normalizedFactors_eq_of_isAmbiguousIdeal
    [IsDedekindDomain OK] {P I : Ideal OK} (hI0 : I ≠ ⊥)
    (hI : IsAmbiguousIdeal (conjAutRingOfIntegers K) I) :
    (UniqueFactorizationMonoid.normalizedFactors I).count
        (Ideal.map (conjAutRingOfIntegers K : OK →+* OK) P) =
      (UniqueFactorizationMonoid.normalizedFactors I).count P := by
  rw [IsAmbiguousIdeal] at hI
  simpa [hI] using
    Ideal.normalizedFactors_count_map_ringEquiv
      (conjAutRingOfIntegers K) (P := P) (I := I) hI0

/-- For an ambiguous nonzero ideal, conjugation preserves the support of its
Dedekind ideal factorization. -/
theorem map_conjAut_mem_normalizedFactors_iff_of_isAmbiguousIdeal
    [IsDedekindDomain OK] {P I : Ideal OK} (hI0 : I ≠ ⊥)
    (hI : IsAmbiguousIdeal (conjAutRingOfIntegers K) I) :
    Ideal.map (conjAutRingOfIntegers K : OK →+* OK) P ∈
        UniqueFactorizationMonoid.normalizedFactors I ↔
      P ∈ UniqueFactorizationMonoid.normalizedFactors I := by
  have hcount :=
    map_conjAut_count_normalizedFactors_eq_of_isAmbiguousIdeal
      (K := K) (P := P) (I := I) hI0 hI
  rw [← Multiset.count_pos, hcount, Multiset.count_pos]

end ConjugationIdealFactors

/-! ## Conjugation as inversion on the ordinary class group -/

section PrimeRelNorm

variable (K : Type*) [Field K] [NumberField K] [Algebra ℚ K] [QuadraticField K]

local notation "OK" => NumberField.RingOfIntegers K

/-- For a nonzero prime ideal `P` of `𝓞 K`, its relative ideal norm over `ℤ` is
the prime below `P`, raised to the inertia degree. -/
theorem relNorm_eq_comap_pow_inertiaDeg_of_isPrime
    (P : Ideal OK) [P.IsPrime] (hP0 : P ≠ ⊥) :
    Ideal.relNorm ℤ P =
      (P.comap (algebraMap ℤ OK)) ^
        P.inertiaDeg ℤ := by
  haveI : IsGalois ℚ K := Algebra.IsQuadraticExtension.isGalois ℚ K
  haveI : IsGalois (FractionRing ℤ) (FractionRing OK) :=
    NumberField.isGalois_fractionRing_ringOfIntegers K
  haveI : P.IsMaximal := Ideal.IsPrime.isMaximal inferInstance hP0
  haveI : (P.comap (algebraMap ℤ OK)).IsMaximal :=
    Ideal.isMaximal_comap_of_isIntegral_of_isMaximal P
  letI : P.LiesOver (P.comap (algebraMap ℤ OK)) := ⟨rfl⟩
  exact Ideal.relNorm_eq_pow_of_isPrime_isGalois P
    (P.comap (algebraMap ℤ OK))

end PrimeRelNorm

section PrimeConjugation

variable (K : Type*) [Field K] [Algebra ℚ K] [QuadraticField K] [QuadraticField.Conj K]

local notation "OK" => NumberField.RingOfIntegers K

/-- The conjugate of a prime ideal lies over the same rational prime ideal. -/
theorem map_conjAut_liesOver_comap (P : Ideal OK) :
    (Ideal.map (conjAutRingOfIntegers K : OK →+* OK) P).LiesOver
        (P.comap (algebraMap ℤ OK)) := by
  letI : P.LiesOver (P.comap (algebraMap ℤ OK)) := ⟨rfl⟩
  exact Ideal.LiesOver.of_eq_map_equiv
    (P.comap (algebraMap ℤ OK))
    (conjAutRingOfIntegersAlgEquiv K) rfl

/-- The conjugate of a prime ideal is again a prime ideal over the same rational
prime ideal. -/
theorem map_conjAut_mem_primesOver_comap (P : Ideal OK) [P.IsPrime] :
    Ideal.map (conjAutRingOfIntegers K : OK →+* OK) P ∈
        Ideal.primesOver (P.comap (algebraMap ℤ OK)) OK :=
  ⟨Ideal.map_isPrime_of_equiv (conjAutRingOfIntegers K), map_conjAut_liesOver_comap K P⟩

/-- If the prime ideal above the same rational prime is unique, conjugation fixes
that prime ideal. -/
theorem map_conjAut_eq_of_primesOver_comap_eq_singleton
    (P : Ideal OK) [P.IsPrime]
    (hsingleton :
      Ideal.primesOver (P.comap (algebraMap ℤ OK)) OK =
        {P}) :
    Ideal.map (conjAutRingOfIntegers K : OK →+* OK) P = P := by
  have hmem := map_conjAut_mem_primesOver_comap (K := K) P
  rw [hsingleton] at hmem
  simpa using hmem

end PrimeConjugation

section QsqrtdRamifiedConjugation

variable (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)]

local notation "OK" => NumberField.RingOfIntegers (Qsqrtd (d : ℚ))

/-- A prime ideal over a ramified rational prime in `ℚ(√d)` is fixed by
quadratic conjugation. -/
theorem map_conjAut_eq_of_mem_primesOver_of_isRamifiedIn
    {p : ℕ} [Fact p.Prime] {P : Ideal OK}
    (hP : P ∈ Ideal.primesOver (𝔭(p))
      OK)
    (hr : Ideal.IsRamifiedIn (𝔭(p))
      OK) :
    Ideal.map (conjAutRingOfIntegers (Qsqrtd (d : ℚ)) :
      OK →+*
        OK) P = P := by
  have hp0 : (𝔭(p) : Ideal ℤ) ≠ ⊥ := Splitting.pIdeal_ne_bot (Fact.out : Nat.Prime p)
  haveI : (𝔭(p) : Ideal ℤ).IsMaximal := Splitting.pIdeal_isMaximal (Fact.out : Nat.Prime p)
  have hsingletonBase :
    Ideal.primesOver (𝔭(p)) OK = {P} :=
    Ideal.primesOver_eq_singleton_of_isRamifiedIn
      (S := OK) (p := 𝔭(p))
      ringChar_int_ne_two hp0 hP hr
  have hPprime : P.IsPrime := hP.1
  haveI : P.IsPrime := hPprime
  letI : P.LiesOver (𝔭(p)) := hP.2
  have hsingletonComap :
      Ideal.primesOver
          (P.comap (algebraMap ℤ OK))
          OK = {P} := by
    change Ideal.primesOver (P.under ℤ)
      OK = {P}
    rw [← Ideal.LiesOver.over (p := 𝔭(p)) (P := P)]
    exact hsingletonBase
  exact map_conjAut_eq_of_primesOver_comap_eq_singleton
    (K := Qsqrtd (d : ℚ)) P hsingletonComap

/-- An indexed ramified-prime ideal is fixed by quadratic conjugation. -/
theorem isAmbiguousIdeal_ramifiedPrimeIdeal
    (p : RamifiedPrimeIndex d) :
    IsAmbiguousIdeal
      (conjAutRingOfIntegers (Qsqrtd (d : ℚ)))
      (ramifiedPrimeIdeal d p) := by
  classical
  letI : Fact p.1.Prime := ⟨prime_of_mem_ramifiedPrimeIndex d p⟩
  exact map_conjAut_eq_of_mem_primesOver_of_isRamifiedIn (d := d)
    (ramifiedPrimeIdeal_mem_primesOver d p)
    (isRamified_of_mem_ramifiedPrimeIndex d p)

end QsqrtdRamifiedConjugation

section PrimeFactorConjugation

variable (K : Type*) [Field K] [Algebra ℚ K] [QuadraticField K] [QuadraticField.Conj K]

local notation "OK" => NumberField.RingOfIntegers K

/-- If `P` is a prime factor of an ambiguous ideal `I`, then its conjugate is
again a prime factor of `I` and lies over the same rational prime ideal as `P`. -/
theorem map_conjAut_mem_normalizedFactors_and_primesOver_comap_of_isAmbiguousIdeal
    [IsDedekindDomain OK]
    {P I : Ideal OK} (hI0 : I ≠ ⊥)
    (hI : IsAmbiguousIdeal (conjAutRingOfIntegers K) I)
    (hP : P ∈ UniqueFactorizationMonoid.normalizedFactors I) :
    Ideal.map (conjAutRingOfIntegers K : OK →+*
        OK) P ∈ UniqueFactorizationMonoid.normalizedFactors I ∧
      Ideal.map (conjAutRingOfIntegers K : OK →+*
        OK) P ∈
          Ideal.primesOver (P.comap (algebraMap ℤ OK))
            OK := by
  constructor
  · exact (map_conjAut_mem_normalizedFactors_iff_of_isAmbiguousIdeal
      (K := K) (P := P) (I := I) hI0 hI).mpr hP
  · have hPprime : P.IsPrime := (Ideal.mem_normalizedFactors_iff hI0).mp hP |>.1
    haveI : P.IsPrime := hPprime
    exact map_conjAut_mem_primesOver_comap K P

/-- Over a split rational prime, quadratic conjugation swaps the two prime ideals
above it rather than fixing either one. -/
theorem map_conjAut_ne_of_mem_primesOver_of_isSplitIn [NumberField K]
    {p : Ideal ℤ} (hp0 : p ≠ ⊥) [p.IsMaximal]
    {P : Ideal OK}
    (hP : P ∈ Ideal.primesOver p OK)
    (hsplit : Ideal.IsSplitIn p OK) :
    Ideal.map (conjAutRingOfIntegers K :
      OK →+* OK) P ≠ P := by
  intro hfix
  let G := Gal(FractionRing OK / FractionRing ℤ)
  letI := Ring.instAlgebraFractionRing
  letI := IsIntegralClosure.MulSemiringAction ℤ (FractionRing ℤ)
    (FractionRing OK) OK
  have hτstab :
      conjAutFractionRingGal K ∈ MulAction.stabilizer G P := by
    change conjAutFractionRingGal K • P = P
    rw [conjAutFractionRingGal_smul_ideal]
    exact hfix
  have hcard_stab : Nat.card (MulAction.stabilizer G P) = 1 :=
    card_stabilizer_fractionRingGal_eq_one_of_mem_primesOver_of_isSplitIn (K := K)
      hp0 hP hsplit
  haveI : Subsingleton (MulAction.stabilizer G P) :=
    (Nat.card_eq_one_iff_unique.mp hcard_stab).1
  exact conjAutFractionRingGal_ne_one K (Subtype.ext_iff.mp
    (Subsingleton.elim
      (⟨conjAutFractionRingGal K, hτstab⟩ : MulAction.stabilizer G P) 1))

end PrimeFactorConjugation

section NormalizedFactorConjugation

variable (K : Type*) [Field K] [Algebra ℚ K] [QuadraticField K] [QuadraticField.Conj K]

local notation "OK" => NumberField.RingOfIntegers K

/-- Conjugation acts on the normalized prime factors of an ambiguous ideal. -/
noncomputable def conjAutNormalizedFactor [IsDedekindDomain OK]
    {I : (Ideal OK)⁰}
    (hI : IsAmbiguousIdeal (conjAutRingOfIntegers K) (I : Ideal OK))
    (P : {P // P ∈ UniqueFactorizationMonoid.normalizedFactors (I : Ideal OK)}) :
    {P // P ∈ UniqueFactorizationMonoid.normalizedFactors (I : Ideal OK)} := by
  have hI0 : (I : Ideal OK) ≠ ⊥ := nonzeroIdeal_ne_bot I
  exact
    ⟨Ideal.map (conjAutRingOfIntegers K : OK →+* OK) P.1,
      (map_conjAut_mem_normalizedFactors_iff_of_isAmbiguousIdeal
        (K := K) (P := P.1) (I := (I : Ideal OK)) hI0 hI).mpr P.2⟩

/-- Conjugation is an involution on normalized prime factors of an ambiguous
ideal. -/
theorem conjAutNormalizedFactor_involutive [IsDedekindDomain OK]
    {I : (Ideal OK)⁰}
    (hI : IsAmbiguousIdeal (conjAutRingOfIntegers K) (I : Ideal OK))
    (P : {P // P ∈ UniqueFactorizationMonoid.normalizedFactors (I : Ideal OK)}) :
    conjAutNormalizedFactor K hI (conjAutNormalizedFactor K hI P) = P :=
  Subtype.ext (map_conjAut_map_conjAut K P.1)

/-- A normalized factor and its conjugate lie over the same rational prime. -/
theorem conjAutNormalizedFactor_comap_eq [IsDedekindDomain OK]
    {I : (Ideal OK)⁰}
    (hI : IsAmbiguousIdeal (conjAutRingOfIntegers K) (I : Ideal OK))
    (P : {P // P ∈ UniqueFactorizationMonoid.normalizedFactors (I : Ideal OK)}) :
    (conjAutNormalizedFactor K hI P).1.comap (algebraMap ℤ OK) =
      P.1.comap (algebraMap ℤ OK) := by
  have hlies := map_conjAut_liesOver_comap (K := K) P.1
  change
    (Ideal.map (conjAutRingOfIntegers K : OK →+* OK) P.1).comap
        (algebraMap ℤ OK) =
      P.1.comap (algebraMap ℤ OK)
  rw [← Ideal.under_def]
  exact hlies.over.symm

/-- For an ambiguous nonzero ideal, conjugation preserves normalized-factor
multiplicity. -/
theorem normalizedFactors_count_conjAutNormalizedFactor_eq [IsDedekindDomain OK]
    {I : (Ideal OK)⁰}
    (hI : IsAmbiguousIdeal (conjAutRingOfIntegers K) (I : Ideal OK))
    (P : {P // P ∈ UniqueFactorizationMonoid.normalizedFactors (I : Ideal OK)}) :
    (UniqueFactorizationMonoid.normalizedFactors (I : Ideal OK)).count
      (conjAutNormalizedFactor K hI P).1 =
    (UniqueFactorizationMonoid.normalizedFactors (I : Ideal OK)).count P.1 := by
  have hI0 : (I : Ideal OK) ≠ ⊥ := nonzeroIdeal_ne_bot I
  exact
    map_conjAut_count_normalizedFactors_eq_of_isAmbiguousIdeal
      (K := K) (P := P.1) (I := (I : Ideal OK)) hI0 hI

/-- Above a split rational prime, conjugation moves a normalized factor to the
other prime above the same rational prime. -/
theorem conjAutNormalizedFactor_ne_of_isSplitIn
    [NumberField K] [IsDedekindDomain OK]
    {I : (Ideal OK)⁰}
    (hI : IsAmbiguousIdeal (conjAutRingOfIntegers K) (I : Ideal OK))
    (P : {P // P ∈ UniqueFactorizationMonoid.normalizedFactors (I : Ideal OK)})
    {p : ℕ} (hp : p.Prime)
    (hcomap : P.1.comap (algebraMap ℤ OK) = 𝔭(p))
    (hsplit : Ideal.IsSplitIn (𝔭(p)) OK) :
    conjAutNormalizedFactor K hI P ≠ P := by
  have hI0 : (I : Ideal OK) ≠ ⊥ := nonzeroIdeal_ne_bot I
  have hPprime : P.1.IsPrime := (Ideal.mem_normalizedFactors_iff hI0).mp P.2 |>.1
  have hPover : P.1 ∈ Ideal.primesOver (𝔭(p)) OK := ⟨hPprime, ⟨hcomap.symm⟩⟩
  have hpbot : (𝔭(p)) ≠ (⊥ : Ideal ℤ) := Splitting.pIdeal_ne_bot hp
  haveI : (𝔭(p)).IsMaximal := Splitting.pIdeal_isMaximal hp
  have hne :=
    map_conjAut_ne_of_mem_primesOver_of_isSplitIn
      (K := K) (p := 𝔭(p)) hpbot hPover hsplit
  intro hfix
  exact hne (congrArg Subtype.val hfix)

end NormalizedFactorConjugation

section QsqrtdNormalizedFactorConjugation

variable (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)]

local notation "OK" => NumberField.RingOfIntegers (Qsqrtd (d : ℚ))

/-- Ramification of a normalized factor is invariant under conjugation. -/
theorem normalizedFactorIsRamified_conjAutNormalizedFactor_iff
    {I : (Ideal OK)⁰}
    (hI : IsAmbiguousIdeal (conjAutRingOfIntegers (Qsqrtd (d : ℚ))) (I : Ideal OK))
    (P : {P // P ∈ UniqueFactorizationMonoid.normalizedFactors (I : Ideal OK)}) :
    normalizedFactorIsRamified d (conjAutNormalizedFactor (Qsqrtd (d : ℚ)) hI P) ↔
      normalizedFactorIsRamified d P := by
  constructor <;> rintro ⟨p, hp, hcomap, hram⟩ <;> refine ⟨p, hp, ?_, hram⟩
  · rw [← conjAutNormalizedFactor_comap_eq (Qsqrtd (d : ℚ)) hI P]
    exact hcomap
  · rw [conjAutNormalizedFactor_comap_eq (Qsqrtd (d : ℚ)) hI P]
    exact hcomap

end QsqrtdNormalizedFactorConjugation

section QsqrtdFactorContribution

variable (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)]

local notation "OK" => NumberField.RingOfIntegers (Qsqrtd (d : ℚ))

/-- A prime factor of an ambiguous ideal contributes a base-prime principal
factor in each splitting case. This span form preserves the positive rational
generator needed later for the narrow principal multiplier. -/
theorem normalizedFactor_span_cases_of_isAmbiguousIdeal
    {P : Ideal OK}
    {I : (Ideal OK)⁰}
    (hI : IsAmbiguousIdeal (conjAutRingOfIntegers (Qsqrtd (d : ℚ))) I.1)
    (hP : P ∈ UniqueFactorizationMonoid.normalizedFactors I.1)
    {p : ℕ} (hp : p.Prime)
    (hcomap : P.comap
      (algebraMap ℤ OK) = 𝔭(p)) :
    (Ideal.IsSplitIn (𝔭(p)) OK ∧
        P * Ideal.map
          (conjAutRingOfIntegers (Qsqrtd (d : ℚ)) :
            OK →+*
              OK) P =
          Ideal.span ({(p : OK)} : Set
            OK)) ∨
      (Ideal.IsInertIn (𝔭(p)) OK ∧
        P = Ideal.span ({(p : OK)} : Set
          OK)) ∨
        (Ideal.IsRamifiedIn (𝔭(p)) OK ∧
          P ^ 2 = Ideal.span ({(p : OK)} :
            Set OK)) := by
  let R := OK
  have hI0 : I.1 ≠ ⊥ := nonzeroIdeal_ne_bot I
  have hPprime : P.IsPrime := (Ideal.mem_normalizedFactors_iff hI0).mp hP |>.1
  have hPover : P ∈ Ideal.primesOver (𝔭(p)) R := ⟨hPprime, ⟨hcomap.symm⟩⟩
  have hpbot : (𝔭(p)) ≠ (⊥ : Ideal ℤ) := Splitting.pIdeal_ne_bot hp
  haveI : (𝔭(p)).IsMaximal := Splitting.pIdeal_isMaximal hp
  have hmapSpan :
      Ideal.map (algebraMap ℤ R) (𝔭(p)) =
        Ideal.span ({(p : R)} : Set R) :=
    map_pIdeal_eq_span_natCast R p
  haveI : Fact p.Prime := ⟨hp⟩
  rcases QuadraticNumberFields.Splitting.split_or_inert_or_ramified (d := d) p with
    hsplit | hinert | hram
  · have hconjOver :
        Ideal.map (conjAutRingOfIntegers (Qsqrtd (d : ℚ)) : R →+* R) P ∈
          Ideal.primesOver (𝔭(p)) R := by
      rw [← hcomap]
      exact (map_conjAut_mem_normalizedFactors_and_primesOver_comap_of_isAmbiguousIdeal
        (K := Qsqrtd (d : ℚ)) (P := P) (I := I.1) hI0 hI hP).2
    have hne :
        P ≠ Ideal.map (conjAutRingOfIntegers (Qsqrtd (d : ℚ)) : R →+* R) P := by
      have hne' :=
        map_conjAut_ne_of_mem_primesOver_of_isSplitIn
          (K := Qsqrtd (d : ℚ)) (p := 𝔭(p)) hpbot hPover hsplit
      intro hfix
      exact hne' hfix.symm
    have hmap :
      Ideal.map (algebraMap ℤ R) (𝔭(p)) =
          P * Ideal.map (conjAutRingOfIntegers (Qsqrtd (d : ℚ)) : R →+* R) P :=
      Ideal.map_eq_mul_of_isSplitIn_of_mem_primesOver_of_ne
        (S := R) (p := 𝔭(p)) ringChar_int_ne_two hpbot
        hPover hconjOver hne hsplit
    exact Or.inl ⟨hsplit, hmap.symm.trans hmapSpan⟩
  · have hmap :
      Ideal.map (algebraMap ℤ R) (𝔭(p)) = P :=
      Ideal.map_eq_of_isInertIn_of_mem_primesOver
        (S := R) (p := 𝔭(p)) ringChar_int_ne_two hpbot hPover hinert
    exact Or.inr <| Or.inl ⟨hinert, hmap.symm.trans hmapSpan⟩
  · have hmap :
      Ideal.map (algebraMap ℤ R) (𝔭(p)) = P ^ 2 :=
      Ideal.map_eq_sq_of_isRamifiedIn_of_mem_primesOver
        (S := R) (p := 𝔭(p)) ringChar_int_ne_two hpbot hPover hram
    exact Or.inr <| Or.inr ⟨hram, hmap.symm.trans hmapSpan⟩

end QsqrtdFactorContribution

section IdealNormConjugation

variable (K : Type*) [Field K] [NumberField K] [Algebra ℚ K]
  [QuadraticField K] [QuadraticField.Conj K]

local notation "OK" => NumberField.RingOfIntegers K

omit [NumberField K] [Algebra ℚ K] [QuadraticField K] [QuadraticField.Conj K] in
private theorem primesOver_eq_singleton_of_ncard_eq_one_of_mem
    {p : Ideal ℤ} {P : Ideal OK}
    (hcard : (Ideal.primesOver p OK).ncard = 1)
    (hPmem : P ∈ Ideal.primesOver p OK) :
    Ideal.primesOver p OK = {P} := by
  obtain ⟨Q, hQ⟩ := Set.ncard_eq_one.mp hcard
  have hPQ : P = Q := by
    have hmem : P ∈ ({Q} : Set (Ideal OK)) := hQ ▸ hPmem
    simpa using hmem
  rw [hQ, hPQ]

omit [NumberField K] in
private theorem map_conjAut_eq_of_mem_primesOver_singleton
    {p : Ideal ℤ} {P : Ideal OK}
    (hσmem :
      Ideal.map (conjAutRingOfIntegers K : OK →+* OK) P ∈
        Ideal.primesOver p OK)
    (hsingleton : Ideal.primesOver p OK = {P}) :
    Ideal.map (conjAutRingOfIntegers K : OK →+* OK) P = P := by
  rw [hsingleton] at hσmem
  exact hσmem

private theorem map_comap_pow_inertiaDeg_eq_mul_map_conjAut_of_isSplitIn
    {p : Ideal ℤ} {P : Ideal OK} [P.IsPrime]
    (hp0 : p ≠ ⊥) [p.IsMaximal]
    (hPmem : P ∈ Ideal.primesOver p OK)
    (hσmem :
      Ideal.map (conjAutRingOfIntegers K : OK →+* OK) P ∈
        Ideal.primesOver p OK)
    (hsplit : Ideal.IsSplitIn p OK) :
    Ideal.map (algebraMap ℤ OK) (p ^ P.inertiaDeg ℤ) =
      P * Ideal.map (conjAutRingOfIntegers K : OK →+* OK) P := by
  let σP : Ideal OK :=
    Ideal.map (conjAutRingOfIntegers K : OK →+* OK) P
  have hσne : σP ≠ P := by
    simpa [σP] using map_conjAut_ne_of_mem_primesOver_of_isSplitIn K hp0 hPmem hsplit
  haveI : P.LiesOver p := hPmem.2
  have hfP : P.inertiaDeg ℤ = 1 :=
    Ideal.inertiaDeg_eq_one_of_isSplitIn p OK
      ringChar_int_ne_two (P' := P) hsplit
  have hmap :
      Ideal.map (algebraMap ℤ OK) p = P * σP :=
    Ideal.map_eq_mul_of_isSplitIn_of_mem_primesOver_of_ne
      (S := OK) (p := p)
      ringChar_int_ne_two hp0 hPmem hσmem hσne.symm hsplit
  rw [hfP, pow_one, hmap]

private theorem map_comap_pow_inertiaDeg_eq_mul_map_conjAut_of_isInertIn
    {p : Ideal ℤ} {P : Ideal OK} [P.IsPrime]
    (hp0 : p ≠ ⊥) [p.IsMaximal]
    (hPmem : P ∈ Ideal.primesOver p OK)
    (hσmem :
      Ideal.map (conjAutRingOfIntegers K : OK →+* OK) P ∈
        Ideal.primesOver p OK)
    (hinert : Ideal.IsInertIn p OK) :
    Ideal.map (algebraMap ℤ OK) (p ^ P.inertiaDeg ℤ) =
      P * Ideal.map (conjAutRingOfIntegers K : OK →+* OK) P := by
  have hsingleton : Ideal.primesOver p OK = {P} :=
    primesOver_eq_singleton_of_ncard_eq_one_of_mem (K := K) hinert.1 hPmem
  have hσP :
      Ideal.map (conjAutRingOfIntegers K : OK →+* OK) P = P :=
    map_conjAut_eq_of_mem_primesOver_singleton (K := K) hσmem hsingleton
  have hfP : P.inertiaDeg ℤ = 2 := by
    letI : P.LiesOver p := hPmem.2
    exact Ideal.inertiaDeg_eq_two_of_isInertIn p OK
      ringChar_int_ne_two hp0 hinert
  have hmap :
      Ideal.map (algebraMap ℤ OK) p = P :=
    Ideal.map_eq_of_isInertIn_of_mem_primesOver p OK
      ringChar_int_ne_two hp0 hPmem hinert
  rw [hfP, Ideal.map_pow, hmap, hσP, pow_two]

private theorem map_comap_pow_inertiaDeg_eq_mul_map_conjAut_of_isRamifiedIn
    {p : Ideal ℤ} {P : Ideal OK} [P.IsPrime]
    (hp0 : p ≠ ⊥) [p.IsMaximal]
    (hPmem : P ∈ Ideal.primesOver p OK)
    (hσmem :
      Ideal.map (conjAutRingOfIntegers K : OK →+* OK) P ∈
        Ideal.primesOver p OK)
    (hram : Ideal.IsRamifiedIn p OK) :
    Ideal.map (algebraMap ℤ OK) (p ^ P.inertiaDeg ℤ) =
      P * Ideal.map (conjAutRingOfIntegers K : OK →+* OK) P := by
  have hsingleton : Ideal.primesOver p OK = {P} :=
    Ideal.primesOver_eq_singleton_of_isRamifiedIn p OK
      ringChar_int_ne_two hp0 hPmem hram
  have hσP :
      Ideal.map (conjAutRingOfIntegers K : OK →+* OK) P = P :=
    map_conjAut_eq_of_mem_primesOver_singleton (K := K) hσmem hsingleton
  have hfP : P.inertiaDeg ℤ = 1 := by
    letI : P.LiesOver p := hPmem.2
    exact Ideal.inertiaDeg_eq_one_of_isRamifiedIn p OK
      ringChar_int_ne_two hp0 hram
  have hmap :
      Ideal.map (algebraMap ℤ OK) p = P ^ 2 :=
    Ideal.map_eq_sq_of_isRamifiedIn_of_mem_primesOver p OK
      ringChar_int_ne_two hp0 hPmem hram
  rw [hfP, pow_one, hmap, hσP, pow_two]

/-- Prime-ideal form of the Galois-orbit calculation: extending the norm prime
power back to the ring of integers gives the product of `P` with its conjugate. -/
theorem map_comap_pow_inertiaDeg_eq_mul_map_conjAut_of_isPrime
    (P : Ideal OK) [P.IsPrime] (hP0 : P ≠ ⊥) :
    Ideal.map (algebraMap ℤ OK)
        ((P.comap (algebraMap ℤ OK)) ^
          P.inertiaDeg ℤ) =
      P * Ideal.map (conjAutRingOfIntegers K :
        OK →+* OK) P := by
  let p : Ideal ℤ := P.comap (algebraMap ℤ OK)
  haveI : P.IsMaximal := Ideal.IsPrime.isMaximal inferInstance hP0
  haveI : p.IsMaximal := Ideal.isMaximal_comap_of_isIntegral_of_isMaximal P
  have hp0 : p ≠ ⊥ := Ideal.IsIntegral.comap_ne_bot ℤ hP0
  have hPmem : P ∈ Ideal.primesOver p OK := ⟨inferInstance, ⟨rfl⟩⟩
  have hσmem :
      Ideal.map (conjAutRingOfIntegers K :
          OK →+* OK) P ∈
        Ideal.primesOver p OK :=
    map_conjAut_mem_primesOver_comap K P
  have htri :=
    Ideal.split_or_inert_or_ramified p OK
      ringChar_int_ne_two hp0
  change Ideal.map (algebraMap ℤ OK) (p ^ P.inertiaDeg ℤ) =
    P * Ideal.map (conjAutRingOfIntegers K : OK →+* OK) P
  rcases htri with hsplit | hinert | hram
  · exact map_comap_pow_inertiaDeg_eq_mul_map_conjAut_of_isSplitIn
      (K := K) hp0 hPmem hσmem hsplit
  · exact map_comap_pow_inertiaDeg_eq_mul_map_conjAut_of_isInertIn
      (K := K) hp0 hPmem hσmem hinert
  · exact map_comap_pow_inertiaDeg_eq_mul_map_conjAut_of_isRamifiedIn
      (K := K) hp0 hPmem hσmem hram

/-- Prime-ideal case of the conjugation/norm identity. -/
theorem mul_map_conjAut_eq_map_relNorm_of_isPrime
    (P : Ideal OK) [P.IsPrime] :
    P * Ideal.map (conjAutRingOfIntegers K :
        OK →+* OK) P =
      Ideal.map (algebraMap ℤ OK) (Ideal.relNorm ℤ P) := by
  by_cases hP0 : P = ⊥
  · simp [hP0, Ideal.relNorm_bot]
  · rw [relNorm_eq_comap_pow_inertiaDeg_of_isPrime K P hP0,
      map_comap_pow_inertiaDeg_eq_mul_map_conjAut_of_isPrime K P hP0]

/-- Multiplicative assembly of the conjugation/norm identity from the prime
ideal case. -/
theorem mul_map_conjAut_eq_map_relNorm_of_forall_isPrime
    (hprime : ∀ P : Ideal OK, P.IsPrime →
      P * Ideal.map (conjAutRingOfIntegers K :
          OK →+* OK) P =
        Ideal.map (algebraMap ℤ OK) (Ideal.relNorm ℤ P))
    (I : Ideal OK) :
    I * Ideal.map (conjAutRingOfIntegers K :
        OK →+* OK) I =
      Ideal.map (algebraMap ℤ OK) (Ideal.relNorm ℤ I) := by
  by_cases hI : I = ⊥
  · simp [hI, Ideal.relNorm_bot]
  rw [← Ideal.prod_normalizedFactors_eq_self hI]
  refine Multiset.prod_induction
      (fun J : Ideal OK =>
        J * Ideal.map (conjAutRingOfIntegers K :
            OK →+* OK) J =
          Ideal.map (algebraMap ℤ OK) (Ideal.relNorm ℤ J))
      _ ?_ ?_ ?_
  · intro J L hJ hL
    rw [Ideal.map_mul, map_mul, Ideal.map_mul]
    calc
      J * L * (Ideal.map (conjAutRingOfIntegers K :
            OK →+* OK) J *
          Ideal.map (conjAutRingOfIntegers K :
            OK →+* OK) L) =
          (J * Ideal.map (conjAutRingOfIntegers K :
              OK →+* OK) J) *
            (L * Ideal.map (conjAutRingOfIntegers K :
              OK →+* OK) L) := by
        ac_rfl
      _ = Ideal.map (algebraMap ℤ OK) (Ideal.relNorm ℤ J) *
          Ideal.map (algebraMap ℤ OK) (Ideal.relNorm ℤ L) := by
        rw [hJ, hL]
  · simp [Ideal.relNorm_top, Ideal.map_top]
  · intro Q hQ
    rw [Ideal.mem_normalizedFactors_iff hI] at hQ
    exact hprime Q hQ.1

/-- Product of an ideal with its quadratic conjugate is the extension of its
relative norm. -/
theorem mul_map_conjAut_eq_map_relNorm
    (I : Ideal OK) :
    I * Ideal.map (conjAutRingOfIntegers K :
        OK →+* OK) I =
      Ideal.map (algebraMap ℤ OK) (Ideal.relNorm ℤ I) := by
  refine mul_map_conjAut_eq_map_relNorm_of_forall_isPrime K ?_ I
  intro P hP
  haveI : P.IsPrime := hP
  exact mul_map_conjAut_eq_map_relNorm_of_isPrime K P

/-- The product of a nonzero ideal with its quadratic conjugate is principal. -/
theorem exists_span_mul_map_conjAut
    {I : Ideal OK} (hI : I ≠ ⊥) :
    ∃ x : OK, x ≠ 0 ∧
      I * Ideal.map (conjAutRingOfIntegers K :
          OK →+* OK) I =
        Ideal.span {x} := by
  have hrel : Ideal.relNorm ℤ I ≠ ⊥ := by
    rw [ne_eq, ← Ideal.spanNorm_eq, Ideal.spanNorm_eq_bot_iff]
    exact hI
  obtain ⟨n, hn⟩ := IsPrincipalIdealRing.principal (Ideal.relNorm ℤ I)
  rw [Ideal.submodule_span_eq] at hn
  have hn0 : n ≠ 0 := by
    rintro rfl
    exact hrel (by rw [hn, Ideal.span_singleton_eq_bot.mpr rfl])
  refine ⟨algebraMap ℤ OK n, ?_, ?_⟩
  · simpa only [map_zero] using
      (FaithfulSMul.algebraMap_injective ℤ OK).ne hn0
  · rw [mul_map_conjAut_eq_map_relNorm K, hn, Ideal.map_span, Set.image_singleton]

/-- The product of a nonzero ideal with its quadratic conjugate is generated by
its positive absolute norm. This is the narrow-class-group strengthening of
`exists_span_mul_map_conjAut`. -/
theorem mul_map_conjAut_eq_span_absNorm
    (I : Ideal OK) :
    I * Ideal.map (conjAutRingOfIntegers K :
        OK →+* OK) I =
      Ideal.span ({(Ideal.absNorm I :
        OK)} : Set OK) := by
  rw [mul_map_conjAut_eq_map_relNorm K]
  rw [Ideal.relNorm_int]
  exact map_pIdeal_eq_span_natCast OK (Ideal.absNorm I)

end IdealNormConjugation

section NonzeroIdealConjugation

variable (K : Type*) [Field K] [Algebra ℚ K] [QuadraticField K] [QuadraticField.Conj K]

local notation "OK" => NumberField.RingOfIntegers K

/-- Conjugation acts multiplicatively on nonzero integral ideals of a quadratic
field. This nonzero-ideal action is used for ambiguous ideal representatives. -/
noncomputable def conjAutNonzeroIdealMulEquiv :
    (Ideal OK)⁰ ≃* (Ideal OK)⁰ :=
  Ideal.mapRingEquivNonZeroDivisorsMulEquiv (conjAutRingOfIntegers K)

/-- The nonzero-ideal conjugation equivalence is implemented by mapping the
underlying ideal by ring-of-integers conjugation. -/
@[simp]
theorem coe_conjAutNonzeroIdealMulEquiv_apply (I : (Ideal OK)⁰) :
    ((conjAutNonzeroIdealMulEquiv K I : (Ideal OK)⁰) : Ideal OK) =
      Ideal.map (conjAutRingOfIntegers K : OK →+* OK) I.1 :=
  rfl

/-- Nonzero-ideal conjugation is involutive. -/
@[simp]
theorem conjAutNonzeroIdealMulEquiv_apply_apply (I : (Ideal OK)⁰) :
    conjAutNonzeroIdealMulEquiv K (conjAutNonzeroIdealMulEquiv K I) = I :=
  Subtype.ext (map_conjAut_map_conjAut K I.1)

/-- A nonzero integral ideal is ambiguous exactly when it is fixed by the
nonzero-ideal conjugation action. -/
theorem isAmbiguousIdeal_iff_conjAutNonzeroIdealMulEquiv_eq (I : (Ideal OK)⁰) :
    IsAmbiguousIdeal (conjAutRingOfIntegers K) I.1 ↔
      conjAutNonzeroIdealMulEquiv K I = I :=
  ⟨fun hI => Subtype.ext hI, fun hI => congrArg Subtype.val hI⟩

/-- Quadratic conjugation acts on the ordinary ideal class group by inversion. -/
theorem mk0_map_conjAut_eq_inv [NumberField K] (I : (Ideal OK)⁰) :
    ClassGroup.mk0
        ⟨Ideal.map (conjAutRingOfIntegers K : OK →+* OK) (I : Ideal OK),
          map_conjAut_mem_nonZeroDivisors K I.2⟩ =
      (ClassGroup.mk0 I)⁻¹ := by
  have hI : (I : Ideal OK) ≠ ⊥ := nonzeroIdeal_ne_bot I
  rw [ClassGroup.mk0_eq_mk0_inv_iff]
  obtain ⟨x, hx0, hx⟩ := exists_span_mul_map_conjAut K hI
  exact ⟨x, hx0, by rw [mul_comm]; exact hx⟩

/-- Quadratic conjugation acts on the narrow ideal class group by inversion. The
extra input compared with the ordinary class-group statement is positivity: the
principal generator of `I * σ(I)` is the positive integer `absNorm I`. -/
theorem narrowClassGroup_mk0_map_conjAut_eq_inv [NumberField K] (I : (Ideal OK)⁰) :
    NarrowClassGroup.mk0 (conjAutNonzeroIdealMulEquiv K I) =
      (NarrowClassGroup.mk0 I)⁻¹ := by
  let R := OK
  have hI0 : (I : Ideal R) ≠ ⊥ := nonzeroIdeal_ne_bot I
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
        exact Subtype.ext (by
          simpa [R] using mul_map_conjAut_eq_span_absNorm K (I : Ideal R))
      _ = 1 :=
        NarrowClassGroup.mk0_span_singleton_eq_one_of_isTotallyPositive
          hnormR_ne
          (NarrowClassGroup.isTotallyPositive_natCast_fractionRing
            (Ideal.absNorm (I : Ideal R)) (Nat.pos_of_ne_zero hnorm0))
  exact eq_inv_of_mul_eq_one_right hprod

end NonzeroIdealConjugation

end Ambiguous
end ClassGroup
end QuadraticNumberFields
