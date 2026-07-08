/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/

import QNFMathlib.GroupTheory.ZModPiPowHom
import QNFMathlib.RingTheory.ClassGroup.Narrow
import QNFMathlib.RingTheory.Ideal.Norm.AbsNorm
import QuadraticNumberFields.ClassGroup.Ambiguous.Ramified
import QuadraticNumberFields.ClassGroup.Ambiguous.Conjugation
import QuadraticNumberFields.Splitting.Qsqrtd.SqrtD

/-!
# Ramified Parity Homomorphism for Narrow Classes

Defines ramified-prime parity vectors and the homomorphism from those vectors to
the narrow class group.
-/

namespace QuadraticNumberFields
namespace ClassGroup
namespace Ambiguous

open scoped BigOperators nonZeroDivisors NumberField
open scoped QuadraticNumberFields.Splitting

section Qsqrtd

attribute [-instance] DivisionRing.toRatAlgebra

variable (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)]

local notation "OK" => 𝓞 (Qsqrtd (d : ℚ))

/-- The parity-vector domain indexed by rational prime divisors of the field
discriminant. -/
abbrev RamifiedParityVector :=
  RamifiedPrimeIndex d → ZMod 2

/-- The ramified-prime parity homomorphism into the narrow class group.

It sends a vector `v` to
`∏ p, (ramifiedPrimeNarrowClass d p) ^ (v p).val`. -/
noncomputable def ramifiedParityNarrowClassHom :
    Multiplicative (RamifiedParityVector d) →*
      NarrowClassGroup OK :=
  MonoidHom.zmodPiPowHom 2 (ramifiedPrimeNarrowClass d) (by
    intro p
    exact ((Subgroup.mem_twoTorsion_iff (x := ramifiedPrimeNarrowClass d p)).mp
      (ramifiedPrimeNarrowClass_mem_twoTorsion d p)))

@[simp]
theorem ramifiedParityNarrowClassHom_apply
    (v : RamifiedParityVector d) :
    ramifiedParityNarrowClassHom d (Multiplicative.ofAdd v) =
      ∏ p, ramifiedPrimeNarrowClass d p ^ (v p).val := by
  simp [ramifiedParityNarrowClassHom, RamifiedParityVector]

/-- Alias for the ramified-prime parity homomorphism used by the upper-bound
layer. -/
noncomputable abbrev fullRamifiedParityNarrowClassHom :
    Multiplicative (RamifiedParityVector d) →*
      NarrowClassGroup OK :=
  ramifiedParityNarrowClassHom d

theorem fullRamifiedParityNarrowClassHom_apply
    (v : RamifiedParityVector d) :
    fullRamifiedParityNarrowClassHom d (Multiplicative.ofAdd v) =
      ∏ p, ramifiedPrimeNarrowClass d p ^ (v p).val :=
  ramifiedParityNarrowClassHom_apply d v

/-- Kernel membership for the ramified-prime parity map. -/
theorem fullRamifiedParityNarrowClassHom_mem_ker_iff
    (v : RamifiedParityVector d) :
    Multiplicative.ofAdd v ∈ (fullRamifiedParityNarrowClassHom d).ker ↔
      fullRamifiedParityNarrowClassHom d (Multiplicative.ofAdd v) = 1 := by
  rfl

/-- The ramified-prime ideal product attached to a `ZMod 2` parity vector. -/
noncomputable def fullRamifiedParityIdealProduct
    (v : RamifiedParityVector d) : (Ideal OK)⁰ :=
  Finset.univ.prod fun p : RamifiedPrimeIndex d =>
    ramifiedPrimeNonzeroIdeal d p ^ (v p).val

/-- The narrow class of `fullRamifiedParityIdealProduct` evaluates the
ramified-prime parity homomorphism. -/
theorem mk0_fullRamifiedParityIdealProduct
    (v : RamifiedParityVector d) :
    NarrowClassGroup.mk0 (fullRamifiedParityIdealProduct d v) =
      fullRamifiedParityNarrowClassHom d (Multiplicative.ofAdd v) := by
  rw [fullRamifiedParityIdealProduct, fullRamifiedParityNarrowClassHom_apply]
  simp only [map_prod, map_pow, mk0_ramifiedPrimeNonzeroIdeal]

/-- Prime-factor contribution in the narrow class group. A split prime factor
cancels with its conjugate, an inert factor is narrowly principal, and a
ramified factor has square one. -/
theorem factor_contribution_cases_narrowClass
    {I : (Ideal OK)⁰}
    (hI : IsAmbiguousIdeal (conjAutRingOfIntegers (Qsqrtd (d : ℚ))) I.1)
    (P : {P // P ∈ UniqueFactorizationMonoid.normalizedFactors (I : Ideal OK)})
    {p : ℕ} (hp : p.Prime)
    (hcomap : P.1.comap (algebraMap ℤ OK) = 𝔭(p)) :
    (Ideal.IsSplitIn (𝔭(p)) OK ∧
        NarrowClassGroup.mk0 (Ideal.normalizedFactorNonzeroIdeal I P) *
          NarrowClassGroup.mk0
            (Ideal.normalizedFactorNonzeroIdeal I
              (conjAutNormalizedFactor (Qsqrtd (d : ℚ)) hI P)) =
          1) ∨
      (Ideal.IsInertIn (𝔭(p)) OK ∧
        NarrowClassGroup.mk0 (Ideal.normalizedFactorNonzeroIdeal I P) = 1) ∨
        (Ideal.IsRamifiedIn (𝔭(p)) OK ∧
          (NarrowClassGroup.mk0 (Ideal.normalizedFactorNonzeroIdeal I P) :
            NarrowClassGroup OK) ^ 2 = 1) := by
  let σP := conjAutNormalizedFactor (Qsqrtd (d : ℚ)) hI P
  let P0 : (Ideal OK)⁰ := Ideal.normalizedFactorNonzeroIdeal I P
  let σP0 : (Ideal OK)⁰ := Ideal.normalizedFactorNonzeroIdeal I σP
  let spanP0 : (Ideal OK)⁰ :=
    Splitting.natCastSpanNonzeroIdeal d p hp
  have hspanP0_one : NarrowClassGroup.mk0 spanP0 = 1 :=
    mk0_natCastSpanNonzeroIdeal_eq_one d hp
  rcases normalizedFactor_span_cases_of_isAmbiguousIdeal d hI P.2 hp hcomap with
    hsplit | hinert | hram
  · refine Or.inl ⟨hsplit.1, ?_⟩
    have hPσP : P0 * σP0 = spanP0 := Subtype.ext hsplit.2
    rw [← map_mul, hPσP, hspanP0_one]
  · refine Or.inr <| Or.inl ⟨hinert.1, ?_⟩
    exact (congrArg NarrowClassGroup.mk0 (Subtype.ext hinert.2)).trans hspanP0_one
  · refine Or.inr <| Or.inr ⟨hram.1, ?_⟩
    rw [← map_pow, show P0 ^ 2 = spanP0 from Subtype.ext hram.2, hspanP0_one]

/-- Split conjugate normalized factors cancel in the narrow class group, with
matching multiplicities. -/
theorem split_conj_normalizedFactor_powers_eq_one
    {I : (Ideal OK)⁰}
    (hI : IsAmbiguousIdeal (conjAutRingOfIntegers (Qsqrtd (d : ℚ))) (I : Ideal OK))
    (P : {P // P ∈ UniqueFactorizationMonoid.normalizedFactors (I : Ideal OK)})
    {p : ℕ} (hp : p.Prime)
    (hcomap : P.1.comap (algebraMap ℤ OK) = 𝔭(p))
    (hsplit : Ideal.IsSplitIn (𝔭(p)) OK) :
    (NarrowClassGroup.mk0 (Ideal.normalizedFactorNonzeroIdeal I P) :
        NarrowClassGroup OK) ^
          (UniqueFactorizationMonoid.normalizedFactors (I : Ideal OK)).count P.1 *
      (NarrowClassGroup.mk0
          (Ideal.normalizedFactorNonzeroIdeal I (conjAutNormalizedFactor (Qsqrtd (d : ℚ)) hI P)) :
        NarrowClassGroup OK) ^
          (UniqueFactorizationMonoid.normalizedFactors (I : Ideal OK)).count
            (conjAutNormalizedFactor (Qsqrtd (d : ℚ)) hI P).1 =
        1 := by
  let σP := conjAutNormalizedFactor (Qsqrtd (d : ℚ)) hI P
  let P0 : (Ideal OK)⁰ := Ideal.normalizedFactorNonzeroIdeal I P
  let σP0 : (Ideal OK)⁰ := Ideal.normalizedFactorNonzeroIdeal I σP
  have hPover : P.1 ∈ Ideal.primesOver (𝔭(p)) OK :=
    normalizedFactor_mem_primesOver_of_comap d P hcomap
  have hpbot : (𝔭(p)) ≠ (⊥ : Ideal ℤ) := Splitting.pIdeal_ne_bot hp
  haveI : (𝔭(p)).IsMaximal := Splitting.pIdeal_isMaximal hp
  have hσcomap : σP.1.comap (algebraMap ℤ OK) = 𝔭(p) := by
    rw [conjAutNormalizedFactor_comap_eq (Qsqrtd (d : ℚ)) hI P, hcomap]
  have hσPover : σP.1 ∈ Ideal.primesOver (𝔭(p)) OK :=
    normalizedFactor_mem_primesOver_of_comap d σP hσcomap
  have hne : P.1 ≠ σP.1 := by
    have hne' := conjAutNormalizedFactor_ne_of_isSplitIn (Qsqrtd (d : ℚ)) hI P hp hcomap hsplit
    intro h
    exact hne' (Subtype.ext h.symm)
  have hmap : Ideal.map (algebraMap ℤ OK) (𝔭(p)) = P.1 * σP.1 :=
    Ideal.map_eq_mul_of_isSplitIn_of_mem_primesOver_of_ne
      (S := OK) (p := 𝔭(p)) (by norm_num : ringChar ℤ ≠ 2) hpbot
      hPover hσPover hne hsplit
  have hmapSpan :
      Ideal.map (algebraMap ℤ OK) (𝔭(p)) =
        Ideal.span ({(p : OK)} : Set OK) := by
    rw [Ideal.map_span, Set.image_singleton]
    rfl
  let spanP0 : (Ideal OK)⁰ :=
    Splitting.natCastSpanNonzeroIdeal d p hp
  have hspanP0_one : NarrowClassGroup.mk0 spanP0 = 1 :=
    mk0_natCastSpanNonzeroIdeal_eq_one d hp
  have hPσP : P0 * σP0 = spanP0 :=
    Subtype.ext (hmap.symm.trans hmapSpan)
  have hpair_one :
      NarrowClassGroup.mk0 P0 * NarrowClassGroup.mk0 σP0 =
        (1 : NarrowClassGroup OK) := by
    rw [← map_mul, hPσP, hspanP0_one]
  have hcount :
      (UniqueFactorizationMonoid.normalizedFactors (I : Ideal OK)).count σP.1 =
        (UniqueFactorizationMonoid.normalizedFactors (I : Ideal OK)).count P.1 :=
    normalizedFactors_count_conjAutNormalizedFactor_eq (Qsqrtd (d : ℚ)) hI P
  change
    (NarrowClassGroup.mk0 P0 : NarrowClassGroup OK) ^
          (UniqueFactorizationMonoid.normalizedFactors (I : Ideal OK)).count P.1 *
      (NarrowClassGroup.mk0 σP0 : NarrowClassGroup OK) ^
          (UniqueFactorizationMonoid.normalizedFactors (I : Ideal OK)).count σP.1 =
        1
  rw [hcount, ← mul_pow, hpair_one, one_pow]

/-- An inert normalized factor contributes trivially to the narrow class group,
even after raising to its multiplicity. -/
theorem inert_normalizedFactor_power_eq_one
    {I : (Ideal OK)⁰}
    (P : {P // P ∈ UniqueFactorizationMonoid.normalizedFactors (I : Ideal OK)})
    {p : ℕ} (hp : p.Prime)
    (hcomap : P.1.comap (algebraMap ℤ OK) = 𝔭(p))
    (hinert : Ideal.IsInertIn (𝔭(p)) OK) :
    (NarrowClassGroup.mk0 (Ideal.normalizedFactorNonzeroIdeal I P) :
        NarrowClassGroup OK) ^
          (UniqueFactorizationMonoid.normalizedFactors (I : Ideal OK)).count P.1 =
        1 := by
  let P0 : (Ideal OK)⁰ := Ideal.normalizedFactorNonzeroIdeal I P
  have hPover : P.1 ∈ Ideal.primesOver (𝔭(p)) OK :=
    normalizedFactor_mem_primesOver_of_comap d P hcomap
  have hpbot : 𝔭(p) ≠ (⊥ : Ideal ℤ) := Splitting.pIdeal_ne_bot hp
  haveI : (𝔭(p)).IsMaximal := Splitting.pIdeal_isMaximal hp
  have hmap : Ideal.map (algebraMap ℤ OK) (𝔭(p)) = P.1 :=
    Ideal.map_eq_of_isInertIn_of_mem_primesOver
      (S := OK) (p := 𝔭(p)) (by norm_num : ringChar ℤ ≠ 2) hpbot hPover hinert
  have hmapSpan :
      Ideal.map (algebraMap ℤ OK) (𝔭(p)) =
        Ideal.span ({(p : OK)} : Set OK) := by
    rw [Ideal.map_span, Set.image_singleton]
    rfl
  let spanP0 : (Ideal OK)⁰ :=
    Splitting.natCastSpanNonzeroIdeal d p hp
  have hP0 : P0 = spanP0 :=
    Subtype.ext (hmap.symm.trans hmapSpan)
  change
    (NarrowClassGroup.mk0 P0 : NarrowClassGroup OK) ^
          (UniqueFactorizationMonoid.normalizedFactors (I : Ideal OK)).count P.1 =
        1
  rw [hP0, mk0_natCastSpanNonzeroIdeal_eq_one d hp, one_pow]

/-- The product of all non-ramified normalized-factor contributions of an
ambiguous ideal is trivial in the narrow class group. -/
theorem normalizedFactors_nonramified_count_prod_eq_one_of_isAmbiguousIdeal
    (J : (Ideal OK)⁰)
    (hJ : IsAmbiguousIdeal (conjAutRingOfIntegers (Qsqrtd (d : ℚ))) (J : Ideal OK))
    [DecidablePred (fun P :
        {P // P ∈ UniqueFactorizationMonoid.normalizedFactors (J : Ideal OK)} =>
      ¬ normalizedFactorIsRamified d P)] :
    (∏ P ∈
        (UniqueFactorizationMonoid.normalizedFactors (J : Ideal OK)).attach.toFinset with
        ¬ normalizedFactorIsRamified d P,
      (NarrowClassGroup.mk0 (Ideal.normalizedFactorNonzeroIdeal J P) :
        NarrowClassGroup OK) ^
        (UniqueFactorizationMonoid.normalizedFactors (J : Ideal OK)).count P.1) =
      1 := by
  let s := UniqueFactorizationMonoid.normalizedFactors (J : Ideal OK)
  let S := s.attach.toFinset
  let f : {P // P ∈ s} → NarrowClassGroup OK := fun P =>
    (NarrowClassGroup.mk0 (Ideal.normalizedFactorNonzeroIdeal J P) :
        NarrowClassGroup OK) ^ s.count P.1
  let σ : {P // P ∈ s} → {P // P ∈ s} := conjAutNormalizedFactor (Qsqrtd (d : ℚ)) hJ
  change (∏ P ∈ S with ¬ normalizedFactorIsRamified d P, f P) = 1
  refine Finset.prod_involution
    (s := S.filter fun P => ¬ normalizedFactorIsRamified d P)
    (f := f) (g := fun P _hP => σ P) ?_ ?_ ?_ ?_
  · intro P hP
    have hPnonram : ¬ normalizedFactorIsRamified d P := (Finset.mem_filter.mp hP).2
    obtain ⟨p, hp, hcomap, _hdvd⟩ :=
      Ideal.exists_nat_prime_comap_eq_span_and_dvd_absNorm_of_isPrime
        (normalizedFactor_isPrime d P) (normalizedFactor_ne_bot d P)
    rcases factor_contribution_cases_narrowClass d hJ P hp hcomap with
      hsplit | hinert | hram
    · simpa [f, σ, s] using
        split_conj_normalizedFactor_powers_eq_one d hJ P hp hcomap hsplit.1
    · have hP_one : f P = 1 := by
        simpa [f, s] using inert_normalizedFactor_power_eq_one d P hp hcomap hinert.1
      have hσcomap : (σ P).1.comap (algebraMap ℤ OK) = 𝔭(p) := by
        simpa [σ] using
          (conjAutNormalizedFactor_comap_eq (Qsqrtd (d : ℚ)) hJ P).trans hcomap
      have hσ_one : f (σ P) = 1 := by
        simpa [f, σ, s] using
          inert_normalizedFactor_power_eq_one d (conjAutNormalizedFactor (Qsqrtd (d : ℚ)) hJ P)
            hp hσcomap hinert.1
      rw [hP_one, hσ_one, one_mul]
    · exact False.elim (hPnonram ⟨p, hp, hcomap, hram.1⟩)
  · intro P hP hfP
    have hPnonram : ¬ normalizedFactorIsRamified d P := (Finset.mem_filter.mp hP).2
    obtain ⟨p, hp, hcomap, _hdvd⟩ :=
      Ideal.exists_nat_prime_comap_eq_span_and_dvd_absNorm_of_isPrime
        (normalizedFactor_isPrime d P) (normalizedFactor_ne_bot d P)
    rcases factor_contribution_cases_narrowClass d hJ P hp hcomap with
      hsplit | hinert | hram
    · exact conjAutNormalizedFactor_ne_of_isSplitIn (Qsqrtd (d : ℚ)) hJ P hp hcomap hsplit.1
    · exact False.elim <| hfP <| by
        simpa [f, s] using inert_normalizedFactor_power_eq_one d P hp hcomap hinert.1
    · exact False.elim (hPnonram ⟨p, hp, hcomap, hram.1⟩)
  · intro P hP
    rw [Finset.mem_filter]
    refine ⟨by simp [S, σ], ?_⟩
    have hPnonram : ¬ normalizedFactorIsRamified d P := (Finset.mem_filter.mp hP).2
    intro hσram
    exact hPnonram ((normalizedFactorIsRamified_conjAutNormalizedFactor_iff d hJ P).mp hσram)
  · intro P _hP
    exact conjAutNormalizedFactor_involutive (Qsqrtd (d : ℚ)) hJ P

/-- The ramified normalized-factor contribution is the product over indexed
ramified-prime ideals, counted by multiplicity. -/
theorem normalizedFactors_ramified_count_prod_eq_ramifiedPrime_count_prod
    (J : (Ideal OK)⁰)
    [DecidablePred (fun P :
        {P // P ∈ UniqueFactorizationMonoid.normalizedFactors (J : Ideal OK)} =>
      normalizedFactorIsRamified d P)] :
    (∏ P ∈
        (UniqueFactorizationMonoid.normalizedFactors (J : Ideal OK)).attach.toFinset with
        normalizedFactorIsRamified d P,
      (NarrowClassGroup.mk0 (Ideal.normalizedFactorNonzeroIdeal J P) :
        NarrowClassGroup OK) ^
        (UniqueFactorizationMonoid.normalizedFactors (J : Ideal OK)).count P.1) =
      Finset.univ.prod fun p : RamifiedPrimeIndex d =>
        (ramifiedPrimeNarrowClass d p) ^
          (UniqueFactorizationMonoid.normalizedFactors (J : Ideal OK)).count
            (ramifiedPrimeIdeal d p) := by
  let s := UniqueFactorizationMonoid.normalizedFactors (J : Ideal OK)
  let S := s.attach.toFinset
  let f : {P // P ∈ s} → NarrowClassGroup OK := fun P =>
    (NarrowClassGroup.mk0 (Ideal.normalizedFactorNonzeroIdeal J P) :
        NarrowClassGroup OK) ^ s.count P.1
  let term : RamifiedPrimeIndex d → NarrowClassGroup OK := fun p =>
    (ramifiedPrimeNarrowClass d p) ^ s.count (ramifiedPrimeIdeal d p)
  let T := Finset.univ.filter fun p : RamifiedPrimeIndex d =>
    ramifiedPrimeIdeal d p ∈ s
  have hleft :
      (∏ P ∈ S with normalizedFactorIsRamified d P, f P) = ∏ p ∈ T, term p := by
    simpa [T] using
      normalizedFactors_ramified_prod_eq_ramifiedPrimeIndex_filter_prod d J f term (by
        intro P hPram
        let p := ramifiedPrimeIndexOfNormalizedFactor d P hPram
        have hP_eq :
            P.1 = ramifiedPrimeIdeal d p :=
          normalizedFactor_eq_ramifiedPrimeIdeal_ramifiedPrimeIndexOfNormalizedFactor
            d P hPram
        have hmk :
            NarrowClassGroup.mk0 (Ideal.normalizedFactorNonzeroIdeal J P) =
              ramifiedPrimeNarrowClass d p := by
          rw [← mk0_ramifiedPrimeNonzeroIdeal d p]
          exact congrArg NarrowClassGroup.mk0 (Subtype.ext hP_eq)
        dsimp [f, term, p]
        rw [hmk, hP_eq])
  have hright :
      (∏ p ∈ T, term p) =
        Finset.univ.prod fun p : RamifiedPrimeIndex d =>
          (ramifiedPrimeNarrowClass d p) ^
            (UniqueFactorizationMonoid.normalizedFactors (J : Ideal OK)).count
              (ramifiedPrimeIdeal d p) := by
    simpa [T, term, s] using
      ramifiedPrimeIndex_filter_prod_eq_univ_prod_of_not_mem_eq_one d J term (by
        intro p hmem
        have hcount0 : s.count (ramifiedPrimeIdeal d p) = 0 :=
          Multiset.count_eq_zero_of_notMem hmem
        simp [term, hcount0])
  exact hleft.trans hright

/-- The full ramified-prime parity vector of a nonzero integral ideal. -/
noncomputable def fullRamifiedParityVector
    (I : (Ideal OK)⁰) : RamifiedParityVector d :=
  fun p : RamifiedPrimeIndex d =>
    ((UniqueFactorizationMonoid.normalizedFactors (I : Ideal OK)).count
      (ramifiedPrimeIdeal d p) : ZMod 2)

/-- An indexed ramified-prime ideal has nonzero parity at its own coordinate. -/
theorem fullRamifiedParityVector_ramifiedPrimeNonzeroIdeal_self_ne_zero
    (p : RamifiedPrimeIndex d) :
    fullRamifiedParityVector d (ramifiedPrimeNonzeroIdeal d p) p ≠ 0 := by
  let P : Ideal OK := ramifiedPrimeIdeal d p
  have hPmem : P ∈ Ideal.primesOver (𝔭(p.1)) OK := by
    simpa [P] using ramifiedPrimeIdeal_mem_primesOver d p
  have hPprime : P.IsPrime := hPmem.1
  have hP0 : P ≠ ⊥ := by
    simpa [P] using ramifiedPrimeIdeal_ne_bot d p
  have hPprimeElem : Prime P := (Ideal.prime_iff_isPrime hP0).mpr hPprime
  have hPirr : Irreducible P := hPprimeElem.irreducible
  have hnf : UniqueFactorizationMonoid.normalizedFactors P = {P} := by
    rw [UniqueFactorizationMonoid.normalizedFactors_irreducible hPirr]
    simp [P]
  change ((UniqueFactorizationMonoid.normalizedFactors P).count P : ZMod 2) ≠ 0
  rw [hnf]
  norm_num

/-- A ramified prime narrow-class power only depends on the parity of the
corresponding normalized-factor count. -/
theorem ramifiedPrimeNarrowClass_pow_normalizedFactors_count_eq_parity
    (J : (Ideal OK)⁰)
    (p : RamifiedPrimeIndex d) :
    (ramifiedPrimeNarrowClass d p) ^
        (UniqueFactorizationMonoid.normalizedFactors (J : Ideal OK)).count
          (ramifiedPrimeIdeal d p) =
      (ramifiedPrimeNarrowClass d p) ^ (fullRamifiedParityVector d J p).val := by
  let n :=
    (UniqueFactorizationMonoid.normalizedFactors (J : Ideal OK)).count
      (ramifiedPrimeIdeal d p)
  let a := ramifiedPrimeNarrowClass d p
  have ha2 : a ^ 2 = 1 := by
    simpa [a] using
      ((Subgroup.mem_twoTorsion_iff (x := ramifiedPrimeNarrowClass d p)).mp
        (ramifiedPrimeNarrowClass_mem_twoTorsion d p))
  have hval : (fullRamifiedParityVector d J p).val = n % 2 := by
    simp [fullRamifiedParityVector, n, ZMod.val_natCast]
  simpa [a, n, hval] using pow_eq_pow_mod n ha2

/-- Count-powered product formula for an ambiguous integral ideal. Split
conjugate pairs cancel, inert factors are narrowly principal, and ramified
factors give the ramified-prime count product. -/
theorem normalizedFactors_count_prod_eq_ramifiedPrime_count_prod_of_isAmbiguousIdeal
    (J : (Ideal OK)⁰)
    (hJ : IsAmbiguousIdeal (conjAutRingOfIntegers (Qsqrtd (d : ℚ))) (J : Ideal OK)) :
    (∏ P ∈
        (UniqueFactorizationMonoid.normalizedFactors (J : Ideal OK)).attach.toFinset,
      (NarrowClassGroup.mk0 (Ideal.normalizedFactorNonzeroIdeal J P) :
        NarrowClassGroup OK) ^
        (UniqueFactorizationMonoid.normalizedFactors (J : Ideal OK)).count P.1) =
      Finset.univ.prod fun p : RamifiedPrimeIndex d =>
        (ramifiedPrimeNarrowClass d p) ^
          (UniqueFactorizationMonoid.normalizedFactors (J : Ideal OK)).count
            (ramifiedPrimeIdeal d p) := by
  classical
  let s := UniqueFactorizationMonoid.normalizedFactors (J : Ideal OK)
  let S := s.attach.toFinset
  let f : {P // P ∈ s} → NarrowClassGroup OK := fun P =>
    (NarrowClassGroup.mk0 (Ideal.normalizedFactorNonzeroIdeal J P) :
        NarrowClassGroup OK) ^ s.count P.1
  have hnonram :
      (∏ P ∈ S with ¬ normalizedFactorIsRamified d P, f P) = 1 := by
    simpa [S, f, s] using
      normalizedFactors_nonramified_count_prod_eq_one_of_isAmbiguousIdeal d J hJ
  have hram :
      (∏ P ∈ S with normalizedFactorIsRamified d P, f P) =
        Finset.univ.prod fun p : RamifiedPrimeIndex d =>
          (ramifiedPrimeNarrowClass d p) ^
            (UniqueFactorizationMonoid.normalizedFactors (J : Ideal OK)).count
              (ramifiedPrimeIdeal d p) := by
    simpa [S, f, s] using
      normalizedFactors_ramified_count_prod_eq_ramifiedPrime_count_prod d J
  calc
    (∏ P ∈ S, f P) =
        (∏ P ∈ S with ¬ normalizedFactorIsRamified d P, f P) *
          ∏ P ∈ S with normalizedFactorIsRamified d P, f P :=
      (Finset.prod_filter_not_mul_prod_filter S
        (fun P => normalizedFactorIsRamified d P) f).symm
    _ = Finset.univ.prod fun p : RamifiedPrimeIndex d =>
          (ramifiedPrimeNarrowClass d p) ^
            (UniqueFactorizationMonoid.normalizedFactors (J : Ideal OK)).count
              (ramifiedPrimeIdeal d p) := by
      rw [hnonram, hram, one_mul]

/-- An ambiguous integral ideal class is represented by the ramified-prime parity
vector attached to its normalized-factor counts. -/
theorem ambiguousIdeal_mk0_eq_fullRamifiedParityNarrowClassHom
    (J : (Ideal OK)⁰)
    (hJ : IsAmbiguousIdeal (conjAutRingOfIntegers (Qsqrtd (d : ℚ))) (J : Ideal OK)) :
    NarrowClassGroup.mk0 J =
      fullRamifiedParityNarrowClassHom d
        (Multiplicative.ofAdd (fullRamifiedParityVector d J)) := by
  classical
  calc
    NarrowClassGroup.mk0 J =
        ∏ P ∈
            (UniqueFactorizationMonoid.normalizedFactors (J : Ideal OK)).attach.toFinset,
          (NarrowClassGroup.mk0 (Ideal.normalizedFactorNonzeroIdeal J P) :
            NarrowClassGroup OK) ^
            (UniqueFactorizationMonoid.normalizedFactors (J : Ideal OK)).count P.1 :=
      NarrowClassGroup.mk0_eq_normalizedFactors_attach_toFinset_prod J
    _ = Finset.univ.prod fun p : RamifiedPrimeIndex d =>
          (ramifiedPrimeNarrowClass d p) ^
            (UniqueFactorizationMonoid.normalizedFactors (J : Ideal OK)).count
              (ramifiedPrimeIdeal d p) :=
      normalizedFactors_count_prod_eq_ramifiedPrime_count_prod_of_isAmbiguousIdeal d J hJ
    _ = Finset.univ.prod fun p : RamifiedPrimeIndex d =>
          (ramifiedPrimeNarrowClass d p) ^ (fullRamifiedParityVector d J p).val := by
      refine Finset.prod_congr rfl ?_
      intro p _hp
      exact ramifiedPrimeNarrowClass_pow_normalizedFactors_count_eq_parity d J p
    _ = fullRamifiedParityNarrowClassHom d
          (Multiplicative.ofAdd (fullRamifiedParityVector d J)) := by
      rw [fullRamifiedParityNarrowClassHom_apply]

end Qsqrtd

end Ambiguous
end ClassGroup
end QuadraticNumberFields
