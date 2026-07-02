/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/

import QuadraticNumberFields.ClassGroup.GenusTheory.AmbiguousIdeals.Exact

/-!
# Ambiguous-Ideal Recovery

This file turns ambiguous and inversion-fixed narrow classes into explicit
ramified-parity representatives.
-/

namespace QuadraticNumberFields
namespace ClassGroup
namespace GenusTheory

open scoped nonZeroDivisors NumberField Pointwise QuadraticNumberFields.ClassGroup
open scoped QuadraticNumberFields.Splitting

attribute [-instance] DivisionRing.toRatAlgebra
attribute [local instance] FractionRing.liftAlgebra

namespace Internal

/-- Count-powered finite-product assembly for a genuinely ambiguous integral
ideal. In the product over distinct normalized prime factors, split conjugate
pairs cancel, inert factors are narrowly principal, and the ramified fixed
factors leave exactly the ramified-prime count product. -/
theorem normalizedFactors_count_prod_eq_ramifiedPrime_count_prod_of_isAmbiguousIdeal
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

/-- Exact class-level per-factor assembly boundary. A genuinely ambiguous
integral ideal has the same narrow class as the product of the ramified-prime
factors selected by its parity vector. -/
theorem ambiguousIdeal_mk0_eq_fullRamifiedParityIdealProduct_of_factorization
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
      exact normalizedFactors_count_prod_eq_ramifiedPrime_count_prod_of_isAmbiguousIdeal d J hJ
    _ = NarrowClassGroup.mk0
          (fullRamifiedParityIdealProduct d (fullRamifiedParityVector d J)) :=
      htarget_count.symm

/-- Per-factor assembly boundary in class form. A genuinely ambiguous integral
ideal class is the class of the full ramified-prime parity product. -/
theorem ambiguousIdeal_mk0_eq_fullRamifiedParityIdealProduct
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)]
    (J : (Ideal (NumberField.RingOfIntegers (Qsqrtd (d : ℚ))))⁰)
    (hJ : IsAmbiguousIdeal (conjAutRingOfIntegers (Qsqrtd (d : ℚ)))
      (J : Ideal (NumberField.RingOfIntegers (Qsqrtd (d : ℚ))))) :
    NarrowClassGroup.mk0 J =
      NarrowClassGroup.mk0
        (fullRamifiedParityIdealProduct d (fullRamifiedParityVector d J)) := by
  exact ambiguousIdeal_mk0_eq_fullRamifiedParityIdealProduct_of_factorization d J hJ

/-- The full ramified parity ideal product is the multiset product of exactly the
ramified prime ideals whose parity coordinate is nonzero. -/
theorem coe_fullRamifiedParityIdealProduct_eq_filtered_multiset_prod
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)]
    (v : ({p // p ∈ ramifiedPrimes d} → Fin 2)) :
    (fullRamifiedParityIdealProduct d v :
      Ideal (NumberField.RingOfIntegers (Qsqrtd (d : ℚ)))) =
      ((Finset.univ.filter fun p => v p ≠ 0).val.map fun p =>
        ramifiedPrimeIdeal d p.2).prod := by
  classical
  let R := NumberField.RingOfIntegers (Qsqrtd (d : ℚ))
  let P : {p // p ∈ ramifiedPrimes d} → Ideal R := fun p => ramifiedPrimeIdeal d p.2
  let P0 : {p // p ∈ ramifiedPrimes d} → (Ideal R)⁰ :=
    fun p =>
      ⟨P p,
        mem_nonZeroDivisors_iff_ne_zero.mpr (by
          simpa [Ideal.zero_eq_bot, P] using ramifiedPrimeIdeal_ne_bot d p.2)⟩
  change
    (↑(Finset.univ.prod fun p =>
      if v p = 0 then (1 : (Ideal R)⁰) else P0 p) : Ideal R) =
      ((Finset.univ.filter fun p => v p ≠ 0).val.map P).prod
  rw [SubmonoidClass.coe_finset_prod]
  simp only [P0]
  rw [← Finset.prod_eq_multiset_prod
    (s := Finset.univ.filter fun p => v p ≠ 0) (f := P)]
  rw [Finset.prod_filter]
  apply Finset.prod_congr rfl
  intro p _hp
  by_cases hp : v p = 0
  · simp [hp]
  · simp [hp]

/-- Normalized-factor count for full ramified parity products. Each ramified
prime appears in the product with multiplicity exactly the corresponding
`Fin 2` value. -/
theorem normalizedFactors_count_fullRamifiedParityIdealProduct
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)]
    (v : ({p // p ∈ ramifiedPrimes d} → Fin 2))
    (p : {p // p ∈ ramifiedPrimes d}) :
    (UniqueFactorizationMonoid.normalizedFactors
        (fullRamifiedParityIdealProduct d v : Ideal
          (NumberField.RingOfIntegers (Qsqrtd (d : ℚ))))).count
      (ramifiedPrimeIdeal d p.2) = (v p).val := by
  have hramifiedPrimeIdeal_injective :
      Function.Injective fun q : {p // p ∈ ramifiedPrimes d} =>
        ramifiedPrimeIdeal d q.2 := by
    intro q r hqr
    apply Subtype.ext
    exact (ramifiedPrimeIdeal_eq_iff d q.2 r.2).mp hqr
  rw [coe_fullRamifiedParityIdealProduct_eq_filtered_multiset_prod d v]
  let R := NumberField.RingOfIntegers (Qsqrtd (d : ℚ))
  let P : {p // p ∈ ramifiedPrimes d} → Ideal R := fun p => ramifiedPrimeIdeal d p.2
  have hP_injective : Function.Injective P := by
    simpa [P] using hramifiedPrimeIdeal_injective
  have hfiltered_prime :
      ∀ Q ∈ ((Finset.univ.filter fun q => v q ≠ 0).val.map P), Prime Q := by
    intro Q hQ
    rcases Multiset.mem_map.mp hQ with ⟨q, _hq, rfl⟩
    exact (Ideal.prime_iff_isPrime (ramifiedPrimeIdeal_ne_bot d q.2)).mpr
      (ramifiedPrimeIdeal_mem_primesOver d q.2).1
  rw [UniqueFactorizationMonoid.normalizedFactors_prod_of_prime hfiltered_prime]
  change ((Finset.univ.filter fun q => v q ≠ 0).val.map P).count (P p) = (v p).val
  rw [Multiset.count_map_eq_count' P _ hP_injective p]
  by_cases hp : v p = 0
  · have hpnot : p ∉ (Finset.univ.filter fun q => v q ≠ 0).val := by
      rw [Finset.mem_val, Finset.mem_filter]
      exact fun h => h.2 hp
    rw [Multiset.count_eq_zero_of_notMem hpnot]
    simp [hp]
  · have hpval : (v p).val = 1 := by
      have hvp : v p = 1 := Fin.eq_one_of_ne_zero (v p) hp
      rw [hvp]
      rfl
    have hpmem : p ∈ (Finset.univ.filter fun q => v q ≠ 0).val := by
      rw [Finset.mem_val, Finset.mem_filter]
      exact ⟨Finset.mem_univ p, hp⟩
    have hnodup : (Finset.univ.filter fun q => v q ≠ 0).val.Nodup :=
      (Finset.univ.filter fun q => v q ≠ 0).nodup
    rw [Multiset.count_eq_one_of_mem hnodup hpmem, hpval]

/-- The full product built from a parity vector has the expected full ramified
parity vector. -/
theorem fullRamifiedParityVector_fullRamifiedParityIdealProduct
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)]
    (v : ({p // p ∈ ramifiedPrimes d} → Fin 2)) :
    fullRamifiedParityVector d (fullRamifiedParityIdealProduct d v) = v := by
  funext p
  apply Fin.ext
  dsimp [fullRamifiedParityVector]
  rw [normalizedFactors_count_fullRamifiedParityIdealProduct d v p]
  exact Nat.mod_eq_of_lt (v p).isLt

/-- Genus relation in concrete ideal form, derived from the uniform Chevalley
kernel boundary.

There is a narrow-trivial ambiguous integral ideal whose ramified-prime parity
vector is nonzero — i.e. a totally-positive-principal ambiguous ideal with
genuinely odd ramified content. The relation is genuinely `d`-dependent, so no
uniform witness exists: e.g. `d = 3` needs the parity vector `(P₂, P₃) = (1, 1)`,
whereas `d = -5` needs `(P₂, P₅) = (0, 1)`. -/
theorem exists_narrowTrivial_ambiguousIdeal_with_ramifiedParity
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] :
    ∃ J : (Ideal (NumberField.RingOfIntegers (Qsqrtd (d : ℚ))))⁰,
      IsAmbiguousIdeal (conjAutRingOfIntegers (Qsqrtd (d : ℚ)))
          (J : Ideal (NumberField.RingOfIntegers (Qsqrtd (d : ℚ)))) ∧
        NarrowClassGroup.mk0 J = 1 ∧
        ∃ p, fullRamifiedParityVector d J p ≠ 0 := by
  obtain ⟨r, hrnonzero, hr⟩ := exists_nonzero_fullRamifiedParityNarrowClassProduct_eq_one d
  let J := fullRamifiedParityIdealProduct d r
  refine ⟨J, ?_, ?_, ?_⟩
  · exact isAmbiguousIdeal_fullRamifiedParityIdealProduct d r
  · rw [mk0_fullRamifiedParityIdealProduct]
    exact hr
  · obtain ⟨p, hp⟩ := hrnonzero
    refine ⟨p, ?_⟩
    simpa [J, fullRamifiedParityVector_fullRamifiedParityIdealProduct d r] using hp

/-- An ambiguous integral ideal class can be represented by the full ramified
parity product, and that representative carries the expected full parity
vector. -/
theorem exists_integralIdeal_fullRamifiedParityRepresentative_of_isAmbiguousIdeal
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)]
    (J : (Ideal (NumberField.RingOfIntegers (Qsqrtd (d : ℚ))))⁰)
    (hJ : IsAmbiguousIdeal (conjAutRingOfIntegers (Qsqrtd (d : ℚ)))
      (J : Ideal (NumberField.RingOfIntegers (Qsqrtd (d : ℚ))))) :
    ∃ I : (Ideal (NumberField.RingOfIntegers (Qsqrtd (d : ℚ))))⁰,
      NarrowClassGroup.mk0 I = NarrowClassGroup.mk0 J ∧
        IsAmbiguousIdeal (conjAutRingOfIntegers (Qsqrtd (d : ℚ)))
          (I : Ideal (NumberField.RingOfIntegers (Qsqrtd (d : ℚ)))) ∧
        NarrowClassGroup.mk0 I =
          NarrowClassGroup.mk0
            (fullRamifiedParityIdealProduct d (fullRamifiedParityVector d I)) := by
  let I := fullRamifiedParityIdealProduct d (fullRamifiedParityVector d J)
  refine ⟨I, ?_, ?_, ?_⟩
  · exact (ambiguousIdeal_mk0_eq_fullRamifiedParityIdealProduct d J hJ).symm
  · exact isAmbiguousIdeal_fullRamifiedParityIdealProduct d (fullRamifiedParityVector d J)
  · dsimp [I]
    rw [fullRamifiedParityVector_fullRamifiedParityIdealProduct d
      (fullRamifiedParityVector d J)]

/-- The erased ramified parity ideal product is the multiset product of exactly
the ramified prime ideals whose parity coordinate is nonzero. -/
theorem coe_ramifiedParityIdealProduct_eq_filtered_multiset_prod
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)]
    {p0 : ℕ} (hp0 : p0 ∈ ramifiedPrimes d)
    (w : ({p // p ∈ (ramifiedPrimes d).erase p0} → Fin 2)) :
    (ramifiedParityIdealProduct d hp0 w :
      Ideal (NumberField.RingOfIntegers (Qsqrtd (d : ℚ)))) =
      ((Finset.univ.filter fun p => w p ≠ 0).val.map fun p =>
        ramifiedPrimeIdeal d ((Finset.mem_erase.mp p.2).2)).prod := by
  classical
  let R := NumberField.RingOfIntegers (Qsqrtd (d : ℚ))
  let P : {p // p ∈ (ramifiedPrimes d).erase p0} → Ideal R :=
    fun p => ramifiedPrimeIdeal d ((Finset.mem_erase.mp p.2).2)
  let P0 : {p // p ∈ (ramifiedPrimes d).erase p0} → (Ideal R)⁰ :=
    fun p =>
      ⟨P p,
        mem_nonZeroDivisors_iff_ne_zero.mpr (by
          simpa [Ideal.zero_eq_bot, P] using
            ramifiedPrimeIdeal_ne_bot d ((Finset.mem_erase.mp p.2).2))⟩
  change
    (↑(Finset.univ.prod fun p =>
      if w p = 0 then (1 : (Ideal R)⁰) else P0 p) : Ideal R) =
      ((Finset.univ.filter fun p => w p ≠ 0).val.map P).prod
  rw [SubmonoidClass.coe_finset_prod]
  simp only [P0]
  rw [← Finset.prod_eq_multiset_prod
    (s := Finset.univ.filter fun p => w p ≠ 0) (f := P)]
  rw [Finset.prod_filter]
  apply Finset.prod_congr rfl
  intro p _hp
  by_cases hp : w p = 0
  · simp [hp]
  · simp [hp]

/-- Normalized-factor count for erased ramified parity products. Each erased
ramified prime appears in the product with multiplicity exactly the corresponding
`Fin 2` value. -/
theorem normalizedFactors_count_ramifiedParityIdealProduct
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)]
    {p0 : ℕ} (hp0 : p0 ∈ ramifiedPrimes d)
    (w : ({p // p ∈ (ramifiedPrimes d).erase p0} → Fin 2))
    (p : {p // p ∈ (ramifiedPrimes d).erase p0}) :
    (UniqueFactorizationMonoid.normalizedFactors
        (ramifiedParityIdealProduct d hp0 w : Ideal
          (NumberField.RingOfIntegers (Qsqrtd (d : ℚ))))).count
      (ramifiedPrimeIdeal d ((Finset.mem_erase.mp p.2).2)) =
        (w p).val := by
  have hramifiedPrimeIdeal_injective :
      Function.Injective fun q : {p // p ∈ (ramifiedPrimes d).erase p0} =>
        ramifiedPrimeIdeal d ((Finset.mem_erase.mp q.2).2) := by
    intro q r hqr
    apply Subtype.ext
    exact (ramifiedPrimeIdeal_eq_iff d
      ((Finset.mem_erase.mp q.2).2) ((Finset.mem_erase.mp r.2).2)).mp hqr
  rw [coe_ramifiedParityIdealProduct_eq_filtered_multiset_prod d hp0 w]
  let R := NumberField.RingOfIntegers (Qsqrtd (d : ℚ))
  let P : {p // p ∈ (ramifiedPrimes d).erase p0} → Ideal R :=
    fun p => ramifiedPrimeIdeal d ((Finset.mem_erase.mp p.2).2)
  have hP_injective : Function.Injective P := by
    simpa [P] using hramifiedPrimeIdeal_injective
  have hfiltered_prime :
      ∀ Q ∈ ((Finset.univ.filter fun q => w q ≠ 0).val.map P), Prime Q := by
    intro Q hQ
    rcases Multiset.mem_map.mp hQ with ⟨q, _hq, rfl⟩
    exact (Ideal.prime_iff_isPrime
      (ramifiedPrimeIdeal_ne_bot d ((Finset.mem_erase.mp q.2).2))).mpr
      (ramifiedPrimeIdeal_mem_primesOver d ((Finset.mem_erase.mp q.2).2)).1
  rw [UniqueFactorizationMonoid.normalizedFactors_prod_of_prime hfiltered_prime]
  change ((Finset.univ.filter fun q => w q ≠ 0).val.map P).count (P p) = (w p).val
  rw [Multiset.count_map_eq_count' P _ hP_injective p]
  by_cases hp : w p = 0
  · have hpnot : p ∉ (Finset.univ.filter fun q => w q ≠ 0).val := by
      rw [Finset.mem_val, Finset.mem_filter]
      exact fun h => h.2 hp
    rw [Multiset.count_eq_zero_of_notMem hpnot]
    simp [hp]
  · have hpval : (w p).val = 1 := by
      have hwp : w p = 1 := Fin.eq_one_of_ne_zero (w p) hp
      rw [hwp]
      rfl
    have hpmem : p ∈ (Finset.univ.filter fun q => w q ≠ 0).val := by
      rw [Finset.mem_val, Finset.mem_filter]
      exact ⟨Finset.mem_univ p, hp⟩
    have hnodup : (Finset.univ.filter fun q => w q ≠ 0).val.Nodup :=
      (Finset.univ.filter fun q => w q ≠ 0).nodup
    rw [Multiset.count_eq_one_of_mem hnodup hpmem, hpval]

/-- The erased product built from a parity vector has the expected erased
ramified parity vector. -/
theorem idealRamifiedParityVector_ramifiedParityIdealProduct
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)]
    {p0 : ℕ} (hp0 : p0 ∈ ramifiedPrimes d)
    (w : ({p // p ∈ (ramifiedPrimes d).erase p0} → Fin 2)) :
    idealRamifiedParityVector d hp0 (ramifiedParityIdealProduct d hp0 w) = w := by
  funext p
  apply Fin.ext
  dsimp [idealRamifiedParityVector]
  rw [normalizedFactors_count_ramifiedParityIdealProduct d hp0 w p]
  exact Nat.mod_eq_of_lt (w p).isLt

/-- Erased-coordinate representative boundary for ambiguous ideals. A genuinely
ambiguous ideal class has a representative whose erased ramified parity product
recovers its narrow class. -/
theorem exists_integralIdeal_erasedRamifiedParityRepresentative_of_isAmbiguousIdeal
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)]
    {p0 : ℕ} (hp0 : p0 ∈ ramifiedPrimes d)
    (r : ({p // p ∈ ramifiedPrimes d} → Fin 2))
    (hrp0 : r ⟨p0, hp0⟩ ≠ 0)
    (hrker : Multiplicative.ofAdd r ∈ (fullRamifiedParityNarrowClassHom d).ker)
    (J : (Ideal (NumberField.RingOfIntegers (Qsqrtd (d : ℚ))))⁰)
    (hJ : IsAmbiguousIdeal (conjAutRingOfIntegers (Qsqrtd (d : ℚ)))
      (J : Ideal (NumberField.RingOfIntegers (Qsqrtd (d : ℚ))))) :
    ∃ I : (Ideal (NumberField.RingOfIntegers (Qsqrtd (d : ℚ))))⁰,
      NarrowClassGroup.mk0 I = NarrowClassGroup.mk0 J ∧
        NarrowClassGroup.mk0 I =
          NarrowClassGroup.mk0
            (ramifiedParityIdealProduct d hp0 (idealRamifiedParityVector d hp0 I)) := by
  obtain ⟨I₀, hI₀mk0, hI₀amb, hI₀full⟩ :=
    exists_integralIdeal_fullRamifiedParityRepresentative_of_isAmbiguousIdeal d J hJ
  obtain ⟨w, hw⟩ :=
    exists_erasedRamifiedParityProduct_mk0_eq_full_of_mem_ker
      d hp0 r hrp0 hrker I₀
  let I := ramifiedParityIdealProduct d hp0 w
  refine ⟨I, ?_, ?_⟩
  · exact hw.trans (hI₀full.symm.trans hI₀mk0)
  · simp [I, idealRamifiedParityVector_ramifiedParityIdealProduct d hp0 w]

/-- Hard representative selection for the ambiguous bound. It chooses a
representative of an inversion-fixed narrow class whose ramified-prime parity
vector actually represents the same narrow class. Proving this is the remaining
mathematical boundary: use the fixed-class Hilbert-90 adjustment, cancel
split/inert/non-ramified prime-ideal orbits, and apply a nonzero
positive-principal relation among ramified parity vectors. -/
theorem exists_integralIdeal_ramifiedParityRepresentative_of_narrowInversionFixedClass
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)]
    {p0 : ℕ} (hp0 : p0 ∈ ramifiedPrimes d)
    (r : ({p // p ∈ ramifiedPrimes d} → Fin 2))
    (hrp0 : r ⟨p0, hp0⟩ ≠ 0)
    (hrker : Multiplicative.ofAdd r ∈ (fullRamifiedParityNarrowClassHom d).ker)
    (C : NarrowInversionFixedClass (NumberField.RingOfIntegers (Qsqrtd (d : ℚ)))) :
    ∃ I : (Ideal (NumberField.RingOfIntegers (Qsqrtd (d : ℚ))))⁰,
      NarrowClassGroup.mk0 I = C.1 ∧
        NarrowClassGroup.mk0 I =
          NarrowClassGroup.mk0
            (ramifiedParityIdealProduct d hp0 (idealRamifiedParityVector d hp0 I)) := by
  obtain ⟨I, hI, x, hxpos, hconj⟩ :=
    exists_integralIdeal_tp_multiplier_to_conjAut_of_narrowInversionFixedClass
      (Qsqrtd (d : ℚ)) C
  obtain ⟨J, hJmk0, hJamb⟩ :=
    exists_integralIdeal_isAmbiguousIdeal_mk0_eq_of_tp_multiplier_to_conjAut
      d I hxpos hconj
  obtain ⟨J', hJ'mk0, hJ'parity⟩ :=
    exists_integralIdeal_erasedRamifiedParityRepresentative_of_isAmbiguousIdeal
      d hp0 r hrp0 hrker J hJamb
  refine ⟨J', ?_, hJ'parity⟩
  exact hJ'mk0.trans (hJmk0.trans hI)

noncomputable def narrowInversionFixedRepresentativeIdeal
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)]
    {p0 : ℕ} (hp0 : p0 ∈ ramifiedPrimes d)
    (r : ({p // p ∈ ramifiedPrimes d} → Fin 2))
    (hrp0 : r ⟨p0, hp0⟩ ≠ 0)
    (hrker : Multiplicative.ofAdd r ∈ (fullRamifiedParityNarrowClassHom d).ker)
    (C : NarrowInversionFixedClass (NumberField.RingOfIntegers (Qsqrtd (d : ℚ)))) :
    (Ideal (NumberField.RingOfIntegers (Qsqrtd (d : ℚ))))⁰ :=
  Classical.choose
    (exists_integralIdeal_ramifiedParityRepresentative_of_narrowInversionFixedClass
      d hp0 r hrp0 hrker C)

theorem narrowInversionFixedRepresentativeIdeal_mk0
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)]
    {p0 : ℕ} (hp0 : p0 ∈ ramifiedPrimes d)
    (r : ({p // p ∈ ramifiedPrimes d} → Fin 2))
    (hrp0 : r ⟨p0, hp0⟩ ≠ 0)
    (hrker : Multiplicative.ofAdd r ∈ (fullRamifiedParityNarrowClassHom d).ker)
    (C : NarrowInversionFixedClass (NumberField.RingOfIntegers (Qsqrtd (d : ℚ)))) :
    NarrowClassGroup.mk0 (narrowInversionFixedRepresentativeIdeal d hp0 r hrp0 hrker C) =
      C.1 :=
  (Classical.choose_spec
    (exists_integralIdeal_ramifiedParityRepresentative_of_narrowInversionFixedClass
      d hp0 r hrp0 hrker C)).1

theorem narrowInversionFixedRepresentativeIdeal_mk0_eq_ramifiedParityIdealProduct
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)]
    {p0 : ℕ} (hp0 : p0 ∈ ramifiedPrimes d)
    (r : ({p // p ∈ ramifiedPrimes d} → Fin 2))
    (hrp0 : r ⟨p0, hp0⟩ ≠ 0)
    (hrker : Multiplicative.ofAdd r ∈ (fullRamifiedParityNarrowClassHom d).ker)
    (C : NarrowInversionFixedClass (NumberField.RingOfIntegers (Qsqrtd (d : ℚ)))) :
    NarrowClassGroup.mk0 (narrowInversionFixedRepresentativeIdeal d hp0 r hrp0 hrker C) =
      NarrowClassGroup.mk0
        (ramifiedParityIdealProduct d hp0
          (idealRamifiedParityVector d hp0
            (narrowInversionFixedRepresentativeIdeal d hp0 r hrp0 hrker C))) :=
  (Classical.choose_spec
    (exists_integralIdeal_ramifiedParityRepresentative_of_narrowInversionFixedClass
      d hp0 r hrp0 hrker C)).2

noncomputable def narrowInversionFixedClassRamifiedParityVector
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)]
    {p0 : ℕ} (hp0 : p0 ∈ ramifiedPrimes d)
    (r : ({p // p ∈ ramifiedPrimes d} → Fin 2))
    (hrp0 : r ⟨p0, hp0⟩ ≠ 0)
    (hrker : Multiplicative.ofAdd r ∈ (fullRamifiedParityNarrowClassHom d).ker) :
    NarrowInversionFixedClass (NumberField.RingOfIntegers (Qsqrtd (d : ℚ))) →
      ({p // p ∈ (ramifiedPrimes d).erase p0} → Fin 2) := by
  classical
  intro C
  exact idealRamifiedParityVector d hp0
    (narrowInversionFixedRepresentativeIdeal d hp0 r hrp0 hrker C)

/-- Exact remaining fixed-representative recovery input for the ambiguous-ideal
bound. It says that the chosen representative of an inversion-fixed narrow
class differs from the ramified parity ideal product by a totally positive
principal fractional ideal. This is the point where the proof still needs the
fixed-ideal representative/factorization theorem and the nonzero
positive-principal relation for ramified parity vectors. -/
theorem exists_tp_multiplier_representative_to_ramifiedParityIdealProduct
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)]
    {p0 : ℕ} (hp0 : p0 ∈ ramifiedPrimes d)
    (r : ({p // p ∈ ramifiedPrimes d} → Fin 2))
    (hrp0 : r ⟨p0, hp0⟩ ≠ 0)
    (hrker : Multiplicative.ofAdd r ∈ (fullRamifiedParityNarrowClassHom d).ker)
    (C : NarrowInversionFixedClass (NumberField.RingOfIntegers (Qsqrtd (d : ℚ)))) :
    ∃ x : (FractionRing (NumberField.RingOfIntegers (Qsqrtd (d : ℚ))))ˣ,
      NarrowClassGroup.IsTotallyPositive
        (x : FractionRing (NumberField.RingOfIntegers (Qsqrtd (d : ℚ)))) ∧
        FractionalIdeal.mk0
            (FractionRing (NumberField.RingOfIntegers (Qsqrtd (d : ℚ))))
            (narrowInversionFixedRepresentativeIdeal d hp0 r hrp0 hrker C) *
          toPrincipalIdeal (NumberField.RingOfIntegers (Qsqrtd (d : ℚ)))
            (FractionRing (NumberField.RingOfIntegers (Qsqrtd (d : ℚ)))) x =
        FractionalIdeal.mk0
          (FractionRing (NumberField.RingOfIntegers (Qsqrtd (d : ℚ))))
          (ramifiedParityIdealProduct d hp0
            (narrowInversionFixedClassRamifiedParityVector d hp0 r hrp0 hrker C)) := by
  have hclass :
      NarrowClassGroup.mk0 (narrowInversionFixedRepresentativeIdeal d hp0 r hrp0 hrker C) =
        NarrowClassGroup.mk0
          (ramifiedParityIdealProduct d hp0
            (narrowInversionFixedClassRamifiedParityVector d hp0 r hrp0 hrker C)) := by
    simpa [narrowInversionFixedClassRamifiedParityVector] using
      narrowInversionFixedRepresentativeIdeal_mk0_eq_ramifiedParityIdealProduct
        d hp0 r hrp0 hrker C
  exact (NarrowClassGroup.mk0_eq_mk0_iff_exists_fraction_ring).mp hclass

/-- The erased ramified-parity vector chosen for an inversion-fixed narrow class
recovers that class. -/
theorem narrowInversionFixedClass_eq_ramifiedParityNarrowClassProduct
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)]
    {p0 : ℕ} (hp0 : p0 ∈ ramifiedPrimes d)
    (r : ({p // p ∈ ramifiedPrimes d} → Fin 2))
    (hrp0 : r ⟨p0, hp0⟩ ≠ 0)
    (hrker : Multiplicative.ofAdd r ∈ (fullRamifiedParityNarrowClassHom d).ker)
    (C : NarrowInversionFixedClass (NumberField.RingOfIntegers (Qsqrtd (d : ℚ)))) :
    C.1 =
      ramifiedParityNarrowClassProduct d hp0
        (narrowInversionFixedClassRamifiedParityVector d hp0 r hrp0 hrker C) := by
  let I := narrowInversionFixedRepresentativeIdeal d hp0 r hrp0 hrker C
  let J := ramifiedParityIdealProduct d hp0
    (narrowInversionFixedClassRamifiedParityVector d hp0 r hrp0 hrker C)
  have hI_mk0 : NarrowClassGroup.mk0 I = C.1 :=
    narrowInversionFixedRepresentativeIdeal_mk0 d hp0 r hrp0 hrker C
  have hJ_mk0 :
      NarrowClassGroup.mk0 J =
        ramifiedParityNarrowClassProduct d hp0
          (narrowInversionFixedClassRamifiedParityVector d hp0 r hrp0 hrker C) := by
    simpa [J] using mk0_ramifiedParityIdealProduct d hp0
      (narrowInversionFixedClassRamifiedParityVector d hp0 r hrp0 hrker C)
  rw [← hI_mk0, ← hJ_mk0]
  rw [NarrowClassGroup.mk0_eq_mk0_iff_exists_fraction_ring]
  simpa only [I, J] using
    exists_tp_multiplier_representative_to_ramifiedParityIdealProduct d hp0 r hrp0 hrker C

/-- The erased ramified-parity vector attached to inversion-fixed narrow classes
is an injective encoding. -/
theorem narrowInversionFixedClassRamifiedParityVector_injective
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)]
    {p0 : ℕ} (hp0 : p0 ∈ ramifiedPrimes d)
    (r : ({p // p ∈ ramifiedPrimes d} → Fin 2))
    (hrp0 : r ⟨p0, hp0⟩ ≠ 0)
    (hrker : Multiplicative.ofAdd r ∈ (fullRamifiedParityNarrowClassHom d).ker) :
    Function.Injective
      (narrowInversionFixedClassRamifiedParityVector d hp0 r hrp0 hrker) := by
  intro C D hCD
  apply Subtype.ext
  rw [narrowInversionFixedClass_eq_ramifiedParityNarrowClassProduct d hp0 r hrp0 hrker C,
    narrowInversionFixedClass_eq_ramifiedParityNarrowClassProduct d hp0 r hrp0 hrker D]
  exact congrArg (ramifiedParityNarrowClassProduct d hp0) hCD

end Internal

end GenusTheory
end ClassGroup
end QuadraticNumberFields
