/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/

import QuadraticNumberFields.ClassGroup.Genus.AmbiguousIdeals.Representatives

/-!
# Ambiguous-Ideal Upper Bound

This file assembles the ramified-parity representative construction into the
upper bound for narrow class-group two-torsion.
-/

namespace QuadraticNumberFields
namespace ClassGroup
namespace Genus

open scoped nonZeroDivisors NumberField Pointwise QuadraticNumberFields.ClassGroup
open scoped QuadraticNumberFields.Splitting

attribute [-instance] DivisionRing.toRatAlgebra
attribute [local instance] FractionRing.liftAlgebra

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

/-- Per-factor assembly boundary in principal-multiplier form. A genuinely
ambiguous integral ideal differs from the product of its ramified-prime parity
factors by a totally positive principal fractional ideal. -/
theorem exists_tp_multiplier_ambiguousIdeal_to_fullRamifiedParityIdealProduct
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)]
    (J : (Ideal (NumberField.RingOfIntegers (Qsqrtd (d : ℚ))))⁰)
    (hJ : IsAmbiguousIdeal (conjAutRingOfIntegers (Qsqrtd (d : ℚ)))
      (J : Ideal (NumberField.RingOfIntegers (Qsqrtd (d : ℚ))))) :
    ∃ x : (FractionRing (NumberField.RingOfIntegers (Qsqrtd (d : ℚ))))ˣ,
      NarrowClassGroup.IsTotallyPositive
        (x : FractionRing (NumberField.RingOfIntegers (Qsqrtd (d : ℚ)))) ∧
        FractionalIdeal.mk0
            (FractionRing (NumberField.RingOfIntegers (Qsqrtd (d : ℚ)))) J *
          toPrincipalIdeal (NumberField.RingOfIntegers (Qsqrtd (d : ℚ)))
            (FractionRing (NumberField.RingOfIntegers (Qsqrtd (d : ℚ)))) x =
        FractionalIdeal.mk0
          (FractionRing (NumberField.RingOfIntegers (Qsqrtd (d : ℚ))))
          (fullRamifiedParityIdealProduct d (fullRamifiedParityVector d J)) := by
  exact (NarrowClassGroup.mk0_eq_mk0_iff_exists_fraction_ring).mp
    (ambiguousIdeal_mk0_eq_fullRamifiedParityIdealProduct_of_factorization d J hJ)

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

/-- If the distinguished coordinate is zero, the full ramified parity ideal
product is literally the erased ramified parity ideal product obtained by
restricting the vector away from that coordinate. -/
theorem fullRamifiedParityIdealProduct_eq_ramifiedParityIdealProduct_of_apply_p0_eq_zero
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)]
    {p0 : ℕ} (hp0 : p0 ∈ ramifiedPrimes d)
    (v : ({p // p ∈ ramifiedPrimes d} → Fin 2))
    (hv0 : v ⟨p0, hp0⟩ = 0) :
    fullRamifiedParityIdealProduct d v =
      ramifiedParityIdealProduct d hp0
        (fun p : {p // p ∈ (ramifiedPrimes d).erase p0} =>
          v ⟨p.1, (Finset.mem_erase.mp p.2).2⟩) := by
  classical
  let R := NumberField.RingOfIntegers (Qsqrtd (d : ℚ))
  let F : {p // p ∈ ramifiedPrimes d} → (Ideal R)⁰ :=
    fun p =>
      if v p = 0 then 1 else
        ⟨ramifiedPrimeIdeal d p.2,
          mem_nonZeroDivisors_iff_ne_zero.mpr (by
            simpa [Ideal.zero_eq_bot] using ramifiedPrimeIdeal_ne_bot d p.2)⟩
  let G : {p // p ∈ (ramifiedPrimes d).erase p0} → (Ideal R)⁰ :=
    fun p =>
      if v ⟨p.1, (Finset.mem_erase.mp p.2).2⟩ = 0 then 1 else
        ⟨ramifiedPrimeIdeal d ((Finset.mem_erase.mp p.2).2),
          mem_nonZeroDivisors_iff_ne_zero.mpr (by
            simpa [Ideal.zero_eq_bot] using
              ramifiedPrimeIdeal_ne_bot d ((Finset.mem_erase.mp p.2).2))⟩
  change Finset.univ.prod F = Finset.univ.prod G
  have hterm : F ⟨p0, hp0⟩ = 1 := by
    simp [F, hv0]
  rw [← Finset.prod_erase (s := Finset.univ) (a := ⟨p0, hp0⟩) (f := F) hterm]
  symm
  refine Finset.prod_bij
    (fun p _hp => (⟨p.1, (Finset.mem_erase.mp p.2).2⟩ :
      {p // p ∈ ramifiedPrimes d})) ?_ ?_ ?_ ?_
  · intro p _hp
    rw [Finset.mem_erase]
    refine ⟨?_, Finset.mem_univ _⟩
    intro hp
    exact (Finset.mem_erase.mp p.2).1 (Subtype.ext_iff.mp hp)
  · intro p _hp q _hq hpq
    apply Subtype.ext
    exact congrArg (fun x : {p // p ∈ ramifiedPrimes d} => (x : ℕ)) hpq
  · intro q hq
    rw [Finset.mem_erase] at hq
    refine ⟨⟨q.1, Finset.mem_erase.mpr ⟨?_, q.2⟩⟩, Finset.mem_univ _, ?_⟩
    · intro hq0
      exact hq.1 (Subtype.ext hq0)
    · apply Subtype.ext
      rfl
  · intro p _hp
    simp [F]

/-- If the distinguished coordinate is zero, the full ramified parity narrow
class product is the erased product obtained by restricting away from that
coordinate. -/
theorem fullRamifiedParityNarrowClassProduct_eq_erased_of_apply_p0_eq_zero
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)]
    {p0 : ℕ} (hp0 : p0 ∈ ramifiedPrimes d)
    (v : ({p // p ∈ ramifiedPrimes d} → Fin 2))
    (hv0 : v ⟨p0, hp0⟩ = 0) :
    fullRamifiedParityNarrowClassProduct d v =
      ramifiedParityNarrowClassProduct d hp0
        (fun p : {p // p ∈ (ramifiedPrimes d).erase p0} =>
          v ⟨p.1, (Finset.mem_erase.mp p.2).2⟩) := by
  classical
  let F : {p // p ∈ ramifiedPrimes d} →
      NarrowClassGroup (NumberField.RingOfIntegers (Qsqrtd (d : ℚ))) :=
    fun p => if v p = 0 then 1 else ramifiedPrimeNarrowClass d p.2
  let G : {p // p ∈ (ramifiedPrimes d).erase p0} →
      NarrowClassGroup (NumberField.RingOfIntegers (Qsqrtd (d : ℚ))) :=
    fun p =>
      if v ⟨p.1, (Finset.mem_erase.mp p.2).2⟩ = 0 then 1 else
        ramifiedPrimeNarrowClass d ((Finset.mem_erase.mp p.2).2)
  change Finset.univ.prod F = Finset.univ.prod G
  have hterm : F ⟨p0, hp0⟩ = 1 := by
    simp [F, hv0]
  rw [← Finset.prod_erase (s := Finset.univ) (a := ⟨p0, hp0⟩) (f := F) hterm]
  symm
  refine Finset.prod_bij
    (fun p _hp => (⟨p.1, (Finset.mem_erase.mp p.2).2⟩ :
      {p // p ∈ ramifiedPrimes d})) ?_ ?_ ?_ ?_
  · intro p _hp
    rw [Finset.mem_erase]
    refine ⟨?_, Finset.mem_univ _⟩
    intro hp
    exact (Finset.mem_erase.mp p.2).1 (Subtype.ext_iff.mp hp)
  · intro p _hp q _hq hpq
    apply Subtype.ext
    exact congrArg (fun x : {p // p ∈ ramifiedPrimes d} => (x : ℕ)) hpq
  · intro q hq
    rw [Finset.mem_erase] at hq
    refine ⟨⟨q.1, Finset.mem_erase.mpr ⟨?_, q.2⟩⟩, Finset.mem_univ _, ?_⟩
    · intro hq0
      exact hq.1 (Subtype.ext hq0)
    · apply Subtype.ext
      rfl
  · intro p _hp
    simp [F]

/-- In `Fin 2`, two nonzero elements add to zero. -/
theorem fin_two_add_eq_zero_of_ne_zero_of_ne_zero {a b : Fin 2}
    (ha : a ≠ 0) (hb : b ≠ 0) : a + b = 0 := by
  have ha1 : a = 1 := Fin.eq_one_of_ne_zero a ha
  have hb1 : b = 1 := Fin.eq_one_of_ne_zero b hb
  simp [ha1, hb1]

/-- A full ramified parity vector lies in the kernel of the narrow-class map
exactly when the corresponding integral ideal product is killed by a totally
positive principal fractional ideal. -/
theorem fullRamifiedParityNarrowClassHom_mem_ker_iff_exists_positivePrincipal
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)]
    (r : {p // p ∈ ramifiedPrimes d} → Fin 2) :
    let R := NumberField.RingOfIntegers (Qsqrtd (d : ℚ))
    Multiplicative.ofAdd r ∈ (fullRamifiedParityNarrowClassHom d).ker ↔
      ∃ x : (FractionRing R)ˣ,
        NarrowClassGroup.IsTotallyPositive (x : FractionRing R) ∧
          FractionalIdeal.mk0 (FractionRing R) (fullRamifiedParityIdealProduct d r) *
            toPrincipalIdeal R (FractionRing R) x = 1 := by
  let R := NumberField.RingOfIntegers (Qsqrtd (d : ℚ))
  rw [fullRamifiedParityNarrowClassHom_mem_ker_iff]
  rw [← mk0_fullRamifiedParityIdealProduct d r]
  exact NarrowClassGroup.mk0_eq_one_iff_exists_fraction_ring

/-- The weak ramified narrow relation is equivalently a nonzero ramified parity
vector whose integral ideal product is killed by a totally positive principal
fractional ideal. -/
theorem exists_nonzero_fullRamifiedParityProduct_eq_one_iff_positivePrincipal
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] :
    (∃ r : ({p // p ∈ ramifiedPrimes d} → Fin 2),
      (∃ p, r p ≠ 0) ∧ fullRamifiedParityNarrowClassProduct d r = 1) ↔
    let R := NumberField.RingOfIntegers (Qsqrtd (d : ℚ))
    ∃ r : ({p // p ∈ ramifiedPrimes d} → Fin 2),
      (∃ p, r p ≠ 0) ∧
        ∃ x : (FractionRing R)ˣ,
          NarrowClassGroup.IsTotallyPositive (x : FractionRing R) ∧
            FractionalIdeal.mk0 (FractionRing R) (fullRamifiedParityIdealProduct d r) *
              toPrincipalIdeal R (FractionRing R) x = 1 := by
  let R := NumberField.RingOfIntegers (Qsqrtd (d : ℚ))
  constructor
  · rintro ⟨r, hrnonzero, hr⟩
    refine ⟨r, hrnonzero, ?_⟩
    exact (fullRamifiedParityNarrowClassHom_mem_ker_iff_exists_positivePrincipal d r).mp
      ((fullRamifiedParityNarrowClassHom_mem_ker_iff d r).mpr hr)
  · rintro ⟨r, hrnonzero, hx⟩
    refine ⟨r, hrnonzero, ?_⟩
    exact (fullRamifiedParityNarrowClassHom_mem_ker_iff d r).mp
      ((fullRamifiedParityNarrowClassHom_mem_ker_iff_exists_positivePrincipal d r).mpr hx)

/-- A full ramified parity class is trivial exactly when adding that vector to
every full parity vector leaves the associated narrow class unchanged. -/
theorem fullRamifiedParityNarrowClassProduct_eq_one_iff_mk0_add_relation
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)]
    (r : {p // p ∈ ramifiedPrimes d} → Fin 2) :
    fullRamifiedParityNarrowClassProduct d r = 1 ↔
      ∀ v : ({p // p ∈ ramifiedPrimes d} → Fin 2),
        NarrowClassGroup.mk0 (fullRamifiedParityIdealProduct d (fun p => v p + r p)) =
          NarrowClassGroup.mk0 (fullRamifiedParityIdealProduct d v) := by
  constructor
  · intro hr v
    rw [mk0_fullRamifiedParityIdealProduct, mk0_fullRamifiedParityIdealProduct]
    rw [fullRamifiedParityNarrowClassProduct_add, hr, mul_one]
  · intro hrel
    have hzero := hrel 0
    rw [mk0_fullRamifiedParityIdealProduct, mk0_fullRamifiedParityIdealProduct] at hzero
    rw [fullRamifiedParityNarrowClassProduct_add,
      fullRamifiedParityNarrowClassProduct_zero, one_mul] at hzero
    simpa [fullRamifiedParityNarrowClassProduct_zero] using hzero

/-- The positive-principal witness for a full parity vector is equivalent to the
translation relation used to erase one ramified coordinate. -/
theorem fullRamifiedParityProduct_positivePrincipal_iff_mk0_add_relation
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)]
    (r : {p // p ∈ ramifiedPrimes d} → Fin 2) :
    let R := NumberField.RingOfIntegers (Qsqrtd (d : ℚ))
    (∃ x : (FractionRing R)ˣ,
      NarrowClassGroup.IsTotallyPositive (x : FractionRing R) ∧
        FractionalIdeal.mk0 (FractionRing R) (fullRamifiedParityIdealProduct d r) *
          toPrincipalIdeal R (FractionRing R) x = 1) ↔
      ∀ v : ({p // p ∈ ramifiedPrimes d} → Fin 2),
        NarrowClassGroup.mk0 (fullRamifiedParityIdealProduct d (fun p => v p + r p)) =
          NarrowClassGroup.mk0 (fullRamifiedParityIdealProduct d v) := by
  let R := NumberField.RingOfIntegers (Qsqrtd (d : ℚ))
  constructor
  · intro hx
    exact (fullRamifiedParityNarrowClassProduct_eq_one_iff_mk0_add_relation d r).mp
      ((fullRamifiedParityNarrowClassHom_mem_ker_iff d r).mp
        ((fullRamifiedParityNarrowClassHom_mem_ker_iff_exists_positivePrincipal d r).mpr hx))
  · intro hrel
    exact (fullRamifiedParityNarrowClassHom_mem_ker_iff_exists_positivePrincipal d r).mp
      ((fullRamifiedParityNarrowClassHom_mem_ker_iff d r).mpr
        ((fullRamifiedParityNarrowClassProduct_eq_one_iff_mk0_add_relation d r).mpr hrel))

/-- Kernel vectors are exactly full ramified parity products generated by a
totally positive element of the fraction field.

This is the principal-generator form of
`fullRamifiedParityNarrowClassHom_mem_ker_iff_exists_positivePrincipal`: the
positive principal multiplier killing the integral product is inverted so that
the generator itself cuts out the ramified parity product. This is the entry
point for the later Hilbert-90/sign analysis of `σ(γ) / γ`. -/
theorem fullRamifiedParityNarrowClassProduct_eq_one_iff_exists_tp_generator
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)]
    (r : {p // p ∈ ramifiedPrimes d} → Fin 2) :
    let R := NumberField.RingOfIntegers (Qsqrtd (d : ℚ))
    fullRamifiedParityNarrowClassProduct d r = 1 ↔
      ∃ γ : (FractionRing R)ˣ,
        NarrowClassGroup.IsTotallyPositive (γ : FractionRing R) ∧
          toPrincipalIdeal R (FractionRing R) γ =
            FractionalIdeal.mk0 (FractionRing R) (fullRamifiedParityIdealProduct d r) := by
  let R := NumberField.RingOfIntegers (Qsqrtd (d : ℚ))
  constructor
  · intro hr
    obtain ⟨x, hxpos, hx⟩ :=
      (fullRamifiedParityNarrowClassHom_mem_ker_iff_exists_positivePrincipal d r).mp
        ((fullRamifiedParityNarrowClassHom_mem_ker_iff d r).mpr hr)
    refine ⟨x⁻¹, ?_, ?_⟩
    · exact (NarrowClassGroup.totallyPositiveUnits (FractionRing R)).inv_mem hxpos
    · rw [map_inv]
      exact (eq_inv_of_mul_eq_one_left hx).symm
  · rintro ⟨γ, hγpos, hγ⟩
    apply (fullRamifiedParityNarrowClassHom_mem_ker_iff d r).mp
    apply (fullRamifiedParityNarrowClassHom_mem_ker_iff_exists_positivePrincipal d r).mpr
    refine ⟨γ⁻¹, ?_, ?_⟩
    · exact (NarrowClassGroup.totallyPositiveUnits (FractionRing R)).inv_mem hγpos
    · rw [map_inv, hγ, mul_inv_cancel]

private theorem exists_unit_map_algebraMap_eq_of_toPrincipalIdeal_eq_one
    {R : Type*} [CommRing R] [IsDomain R] {x : (FractionRing R)ˣ}
    (hx : toPrincipalIdeal R (FractionRing R) x = 1) :
    ∃ u : Rˣ, Units.map (algebraMap R (FractionRing R)).toMonoidHom u = x := by
  have hspan : FractionalIdeal.spanSingleton R⁰ (x : FractionRing R) = 1 :=
    (toPrincipalIdeal_eq_iff (I := 1) (x := x)).mp hx
  have hx_mem : (x : FractionRing R) ∈ (1 : FractionalIdeal R⁰ (FractionRing R)) := by
    rw [← hspan]
    exact FractionalIdeal.mem_spanSingleton_self R⁰ (x : FractionRing R)
  have hx_inv : toPrincipalIdeal R (FractionRing R) x⁻¹ = 1 := by
    rw [map_inv, hx, inv_one]
  have hspan_inv :
      FractionalIdeal.spanSingleton R⁰ ((x⁻¹ : (FractionRing R)ˣ) : FractionRing R) = 1 :=
    (toPrincipalIdeal_eq_iff (I := 1) (x := x⁻¹)).mp hx_inv
  have hx_inv_mem :
      ((x⁻¹ : (FractionRing R)ˣ) : FractionRing R) ∈
        (1 : FractionalIdeal R⁰ (FractionRing R)) := by
    rw [← hspan_inv]
    exact FractionalIdeal.mem_spanSingleton_self R⁰
      ((x⁻¹ : (FractionRing R)ˣ) : FractionRing R)
  obtain ⟨a, ha⟩ := (FractionalIdeal.mem_one_iff R⁰).mp hx_mem
  obtain ⟨b, hb⟩ := (FractionalIdeal.mem_one_iff R⁰).mp hx_inv_mem
  refine ⟨
    { val := a
      inv := b
      val_inv := ?_
      inv_val := ?_ }, ?_⟩
  · apply FaithfulSMul.algebraMap_injective R (FractionRing R)
    simp [map_mul, ha, hb]
  · apply FaithfulSMul.algebraMap_injective R (FractionRing R)
    simp [map_mul, ha, hb]
  · apply Units.ext
    simp [ha]

/-- If a full ramified parity product is generated by `γ`, then `σγ / γ` has
trivial principal fractional ideal.

This is the first unit-theoretic output of the kernel generator form: the
ramified parity product is ambiguous, so its generator and conjugate generator
cut out the same principal fractional ideal. The next step is to upgrade this
trivial principal ideal statement to an actual unit/sign datum. -/
theorem toPrincipalIdeal_conjAut_mul_inv_eq_one_of_tp_generator
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)]
    (r : {p // p ∈ ramifiedPrimes d} → Fin 2)
    {γ : (FractionRing (NumberField.RingOfIntegers (Qsqrtd (d : ℚ))))ˣ}
    (hγ :
      toPrincipalIdeal (NumberField.RingOfIntegers (Qsqrtd (d : ℚ)))
          (FractionRing (NumberField.RingOfIntegers (Qsqrtd (d : ℚ)))) γ =
        FractionalIdeal.mk0
          (FractionRing (NumberField.RingOfIntegers (Qsqrtd (d : ℚ))))
          (fullRamifiedParityIdealProduct d r)) :
    toPrincipalIdeal (NumberField.RingOfIntegers (Qsqrtd (d : ℚ)))
        (FractionRing (NumberField.RingOfIntegers (Qsqrtd (d : ℚ))))
        (Units.mapEquiv (conjAutFractionRingAlgEquiv (Qsqrtd (d : ℚ))).toRingEquiv γ *
          γ⁻¹) =
      1 := by
  let R := NumberField.RingOfIntegers (Qsqrtd (d : ℚ))
  let K := Qsqrtd (d : ℚ)
  let I := fullRamifiedParityIdealProduct d r
  have hIamb : IsAmbiguousIdeal (conjAutRingOfIntegers K) (I : Ideal R) := by
    simpa [I, K, R] using isAmbiguousIdeal_fullRamifiedParityIdealProduct d r
  have hIconj : conjAutNonzeroIdealMulEquiv K I = I :=
    (isAmbiguousIdeal_iff_conjAutNonzeroIdealMulEquiv_eq K I).mp hIamb
  have hγ_conj :
      toPrincipalIdeal R (FractionRing R)
          (Units.mapEquiv (conjAutFractionRingAlgEquiv K).toRingEquiv γ) =
        toPrincipalIdeal R (FractionRing R) γ := by
    apply Units.ext
    calc
      ((toPrincipalIdeal R (FractionRing R)
              (Units.mapEquiv (conjAutFractionRingAlgEquiv K).toRingEquiv γ)) :
          FractionalIdeal R⁰ (FractionRing R)) =
          FractionalIdeal.ringEquivMap
            (K := FractionRing R) (L := FractionRing R)
            (conjAutRingOfIntegers K)
            (toPrincipalIdeal R (FractionRing R) γ :
              FractionalIdeal R⁰ (FractionRing R)) := by
        rw [ringEquivMap_conjAut_toPrincipalIdeal]
      _ =
          FractionalIdeal.ringEquivMap
            (K := FractionRing R) (L := FractionRing R)
            (conjAutRingOfIntegers K)
            (FractionalIdeal.mk0 (FractionRing R) I) := by
        rw [hγ]
      _ = FractionalIdeal.mk0 (FractionRing R) (conjAutNonzeroIdealMulEquiv K I) := by
        rw [ringEquivMap_conjAut_mk0]
      _ = FractionalIdeal.mk0 (FractionRing R) I := by
        rw [hIconj]
      _ = (toPrincipalIdeal R (FractionRing R) γ :
          FractionalIdeal R⁰ (FractionRing R)) := by
        rw [hγ]
  rw [map_mul, map_inv, hγ_conj, mul_inv_cancel]

/-- If a full ramified parity product is generated by `γ`, then `σγ / γ` is the
image of an integral unit. -/
theorem exists_unit_map_algebraMap_eq_conjAut_mul_inv_of_tp_generator
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)]
    (r : {p // p ∈ ramifiedPrimes d} → Fin 2)
    {γ : (FractionRing (NumberField.RingOfIntegers (Qsqrtd (d : ℚ))))ˣ}
    (hγ :
      toPrincipalIdeal (NumberField.RingOfIntegers (Qsqrtd (d : ℚ)))
          (FractionRing (NumberField.RingOfIntegers (Qsqrtd (d : ℚ)))) γ =
        FractionalIdeal.mk0
          (FractionRing (NumberField.RingOfIntegers (Qsqrtd (d : ℚ))))
          (fullRamifiedParityIdealProduct d r)) :
    ∃ u : (NumberField.RingOfIntegers (Qsqrtd (d : ℚ)))ˣ,
      Units.map
          (algebraMap (NumberField.RingOfIntegers (Qsqrtd (d : ℚ)))
            (FractionRing (NumberField.RingOfIntegers (Qsqrtd (d : ℚ))))).toMonoidHom u =
        Units.mapEquiv (conjAutFractionRingAlgEquiv (Qsqrtd (d : ℚ))).toRingEquiv γ *
          γ⁻¹ := by
  exact exists_unit_map_algebraMap_eq_of_toPrincipalIdeal_eq_one
    (toPrincipalIdeal_conjAut_mul_inv_eq_one_of_tp_generator d r hγ)

private theorem conjAutFractionRingAlgEquiv_apply_apply
    (K : Type*) [Field K] [NumberField K] [Algebra ℚ K]
    [QuadraticField K] [QuadraticField.Conj K]
    (x : FractionRing (NumberField.RingOfIntegers K)) :
    conjAutFractionRingAlgEquiv K (conjAutFractionRingAlgEquiv K x) = x := by
  let R := NumberField.RingOfIntegers K
  have hhom :
      ((conjAutFractionRingAlgEquiv K).toRingHom.comp
          (conjAutFractionRingAlgEquiv K).toRingHom) =
        RingHom.id (FractionRing R) := by
    apply IsFractionRing.ringHom_ext (A := R) (K := FractionRing R)
      (L := FractionRing R)
    intro x
    simp [R, RingHom.comp_apply]
  exact RingHom.congr_fun hhom x

private theorem map_conjAutRingOfIntegers_unit_eq_conjAutFractionRing_map_unit
    (K : Type*) [Field K] [NumberField K] [Algebra ℚ K]
    [QuadraticField K] [QuadraticField.Conj K]
    (u : (NumberField.RingOfIntegers K)ˣ) :
    Units.map
        (algebraMap (NumberField.RingOfIntegers K)
          (FractionRing (NumberField.RingOfIntegers K))).toMonoidHom
        (Units.mapEquiv (conjAutRingOfIntegers K).toMulEquiv u) =
      Units.mapEquiv (conjAutFractionRingAlgEquiv K).toRingEquiv.toMulEquiv
        (Units.map
          (algebraMap (NumberField.RingOfIntegers K)
            (FractionRing (NumberField.RingOfIntegers K))).toMonoidHom u) := by
  apply Units.ext
  simp

/-- If an integral unit maps to `σγ / γ`, then it has quadratic norm one:
`σu * u = 1`. This is the unit-theoretic shape needed before applying the
Hilbert-90/sign analysis. -/
theorem conjAutRingOfIntegers_unit_mul_self_eq_one_of_map_eq_conjAut_mul_inv
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)]
    {γ : (FractionRing (NumberField.RingOfIntegers (Qsqrtd (d : ℚ))))ˣ}
    {u : (NumberField.RingOfIntegers (Qsqrtd (d : ℚ)))ˣ}
    (hu :
      Units.map
          (algebraMap (NumberField.RingOfIntegers (Qsqrtd (d : ℚ)))
            (FractionRing (NumberField.RingOfIntegers (Qsqrtd (d : ℚ))))).toMonoidHom u =
        Units.mapEquiv (conjAutFractionRingAlgEquiv (Qsqrtd (d : ℚ))).toRingEquiv γ *
          γ⁻¹) :
    Units.mapEquiv (conjAutRingOfIntegers (Qsqrtd (d : ℚ))).toMulEquiv u * u = 1 := by
  let R := NumberField.RingOfIntegers (Qsqrtd (d : ℚ))
  let K := Qsqrtd (d : ℚ)
  let σF := Units.mapEquiv (conjAutFractionRingAlgEquiv K).toRingEquiv.toMulEquiv
  let algUnits : Rˣ →* (FractionRing R)ˣ :=
    Units.map (algebraMap R (FractionRing R)).toMonoidHom
  have hσhu : σF (algUnits u) = γ * (σF γ)⁻¹ := by
    rw [hu]
    apply Units.ext
    simp [σF, K, conjAutFractionRingAlgEquiv_apply_apply]
  have hmap :
      algUnits (Units.mapEquiv (conjAutRingOfIntegers K).toMulEquiv u * u) = 1 := by
    rw [map_mul]
    rw [map_conjAutRingOfIntegers_unit_eq_conjAutFractionRing_map_unit]
    rw [hσhu, hu]
    change γ * (σF γ)⁻¹ * (σF γ * γ⁻¹) = 1
    calc
      γ * (σF γ)⁻¹ * (σF γ * γ⁻¹) = γ * ((σF γ)⁻¹ * σF γ) * γ⁻¹ := by
        ac_rfl
      _ = γ * 1 * γ⁻¹ := by
        rw [inv_mul_cancel]
      _ = 1 := by
        rw [mul_one, mul_inv_cancel]
  apply Units.ext
  apply FaithfulSMul.algebraMap_injective R (FractionRing R)
  simpa [algUnits, R, K] using Units.ext_iff.mp hmap

/-- For a generator of a full ramified parity product, the integral unit
representing `σγ / γ` may be chosen with quadratic norm one. -/
theorem exists_normOne_unit_map_algebraMap_eq_conjAut_mul_inv_of_tp_generator
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)]
    (r : {p // p ∈ ramifiedPrimes d} → Fin 2)
    {γ : (FractionRing (NumberField.RingOfIntegers (Qsqrtd (d : ℚ))))ˣ}
    (hγ :
      toPrincipalIdeal (NumberField.RingOfIntegers (Qsqrtd (d : ℚ)))
          (FractionRing (NumberField.RingOfIntegers (Qsqrtd (d : ℚ)))) γ =
        FractionalIdeal.mk0
          (FractionRing (NumberField.RingOfIntegers (Qsqrtd (d : ℚ))))
          (fullRamifiedParityIdealProduct d r)) :
    ∃ u : (NumberField.RingOfIntegers (Qsqrtd (d : ℚ)))ˣ,
      Units.map
          (algebraMap (NumberField.RingOfIntegers (Qsqrtd (d : ℚ)))
            (FractionRing (NumberField.RingOfIntegers (Qsqrtd (d : ℚ))))).toMonoidHom u =
          Units.mapEquiv (conjAutFractionRingAlgEquiv (Qsqrtd (d : ℚ))).toRingEquiv γ *
            γ⁻¹ ∧
        Units.mapEquiv (conjAutRingOfIntegers (Qsqrtd (d : ℚ))).toMulEquiv u * u = 1 := by
  obtain ⟨u, hu⟩ := exists_unit_map_algebraMap_eq_conjAut_mul_inv_of_tp_generator d r hγ
  exact ⟨u, hu, conjAutRingOfIntegers_unit_mul_self_eq_one_of_map_eq_conjAut_mul_inv d hu⟩

/-- Chevalley's narrow ambiguous class number formula, in the only form needed
for the upper bound.

This is the genuine global mathematical boundary: the full ramified parity map
has a nonzero kernel vector. Equivalently, the narrow-principal ambiguous ideals
form a codimension-one subspace of the ramified parity space, the `-1` in
`|Am⁺| = 2 ^ (t - 1)`. This statement is uniform in `d`; the witness vector is
not. -/
theorem exists_nonzero_fullRamifiedParityNarrowClassProduct_eq_one_of_chevalley
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] :
    ∃ r : ({p // p ∈ ramifiedPrimes d} → Fin 2),
      (∃ p, r p ≠ 0) ∧ fullRamifiedParityNarrowClassProduct d r = 1 := by
  sorry

/-- Weak positive-principal ramified relation needed for the upper bound. It
asserts that some nonzero product of ramified prime ideal classes is trivial in
the narrow class group.

This is weaker than computing the full kernel of the ramified parity map. It is
the only global unit/sign input needed to erase one ramified coordinate in the
upper-bound proof, and is exactly the Chevalley kernel-nontriviality boundary
recorded in
`exists_nonzero_fullRamifiedParityNarrowClassProduct_eq_one_of_chevalley`. -/
theorem exists_nonzero_fullRamifiedParityNarrowClassProduct_eq_one
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] :
    ∃ r : ({p // p ∈ ramifiedPrimes d} → Fin 2),
      (∃ p, r p ≠ 0) ∧ fullRamifiedParityNarrowClassProduct d r = 1 := by
  exact exists_nonzero_fullRamifiedParityNarrowClassProduct_eq_one_of_chevalley d

/-- A nonzero kernel vector for the finite ramified parity map acts trivially on
all full ramified parity products. -/
theorem exists_nonzero_positivePrincipalRamifiedParityRelation
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] :
    ∃ r : ({p // p ∈ ramifiedPrimes d} → Fin 2),
      (∃ p, r p ≠ 0) ∧
        ∀ v : ({p // p ∈ ramifiedPrimes d} → Fin 2),
          NarrowClassGroup.mk0
              (fullRamifiedParityIdealProduct d (fun p => v p + r p)) =
            NarrowClassGroup.mk0 (fullRamifiedParityIdealProduct d v) := by
  obtain ⟨r, hrnonzero, hr⟩ :=
    exists_nonzero_fullRamifiedParityNarrowClassProduct_eq_one d
  exact ⟨r, hrnonzero,
    (fullRamifiedParityNarrowClassProduct_eq_one_iff_mk0_add_relation d r).mp hr⟩

/-- A nonzero positive-principal ramified parity relation lets us erase any
coordinate in its support. This is the correct replacement for the false
all-one finite ramified relation in the narrow real quadratic case. -/
theorem exists_erasedRamifiedParityProduct_mk0_eq_full_of_relation
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)]
    {p0 : ℕ} (hp0 : p0 ∈ ramifiedPrimes d)
    (r : ({p // p ∈ ramifiedPrimes d} → Fin 2))
    (hrp0 : r ⟨p0, hp0⟩ ≠ 0)
    (hrel : ∀ v : ({p // p ∈ ramifiedPrimes d} → Fin 2),
      NarrowClassGroup.mk0
          (fullRamifiedParityIdealProduct d (fun p => v p + r p)) =
        NarrowClassGroup.mk0 (fullRamifiedParityIdealProduct d v))
    (J : (Ideal (NumberField.RingOfIntegers (Qsqrtd (d : ℚ))))⁰) :
    ∃ w : ({p // p ∈ (ramifiedPrimes d).erase p0} → Fin 2),
      NarrowClassGroup.mk0
          (ramifiedParityIdealProduct d hp0 w) =
        NarrowClassGroup.mk0
          (fullRamifiedParityIdealProduct d (fullRamifiedParityVector d J)) := by
  let v := fullRamifiedParityVector d J
  by_cases hv0 : v ⟨p0, hp0⟩ = 0
  · refine ⟨fun p => v ⟨p.1, (Finset.mem_erase.mp p.2).2⟩, ?_⟩
    rw [fullRamifiedParityIdealProduct_eq_ramifiedParityIdealProduct_of_apply_p0_eq_zero
      d hp0 v hv0]
  · let v' : {p // p ∈ ramifiedPrimes d} → Fin 2 := fun p => v p + r p
    have hv'p0 : v' ⟨p0, hp0⟩ = 0 := by
      simpa [v'] using fin_two_add_eq_zero_of_ne_zero_of_ne_zero hv0 hrp0
    refine ⟨fun p => v' ⟨p.1, (Finset.mem_erase.mp p.2).2⟩, ?_⟩
    rw [← fullRamifiedParityIdealProduct_eq_ramifiedParityIdealProduct_of_apply_p0_eq_zero
      d hp0 v' hv'p0]
    simpa [v'] using hrel v

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
    (hrel : ∀ v : ({p // p ∈ ramifiedPrimes d} → Fin 2),
      NarrowClassGroup.mk0
          (fullRamifiedParityIdealProduct d (fun p => v p + r p)) =
        NarrowClassGroup.mk0 (fullRamifiedParityIdealProduct d v))
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
    exists_erasedRamifiedParityProduct_mk0_eq_full_of_relation
      d hp0 r hrp0 hrel I₀
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
    (hrel : ∀ v : ({p // p ∈ ramifiedPrimes d} → Fin 2),
      NarrowClassGroup.mk0
          (fullRamifiedParityIdealProduct d (fun p => v p + r p)) =
        NarrowClassGroup.mk0 (fullRamifiedParityIdealProduct d v))
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
      d hp0 r hrp0 hrel J hJamb
  refine ⟨J', ?_, hJ'parity⟩
  exact hJ'mk0.trans (hJmk0.trans hI)

noncomputable def narrowInversionFixedRepresentativeIdeal
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)]
    {p0 : ℕ} (hp0 : p0 ∈ ramifiedPrimes d)
    (r : ({p // p ∈ ramifiedPrimes d} → Fin 2))
    (hrp0 : r ⟨p0, hp0⟩ ≠ 0)
    (hrel : ∀ v : ({p // p ∈ ramifiedPrimes d} → Fin 2),
      NarrowClassGroup.mk0
          (fullRamifiedParityIdealProduct d (fun p => v p + r p)) =
        NarrowClassGroup.mk0 (fullRamifiedParityIdealProduct d v))
    (C : NarrowInversionFixedClass (NumberField.RingOfIntegers (Qsqrtd (d : ℚ)))) :
    (Ideal (NumberField.RingOfIntegers (Qsqrtd (d : ℚ))))⁰ :=
  Classical.choose
    (exists_integralIdeal_ramifiedParityRepresentative_of_narrowInversionFixedClass
      d hp0 r hrp0 hrel C)

theorem narrowInversionFixedRepresentativeIdeal_mk0
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)]
    {p0 : ℕ} (hp0 : p0 ∈ ramifiedPrimes d)
    (r : ({p // p ∈ ramifiedPrimes d} → Fin 2))
    (hrp0 : r ⟨p0, hp0⟩ ≠ 0)
    (hrel : ∀ v : ({p // p ∈ ramifiedPrimes d} → Fin 2),
      NarrowClassGroup.mk0
          (fullRamifiedParityIdealProduct d (fun p => v p + r p)) =
        NarrowClassGroup.mk0 (fullRamifiedParityIdealProduct d v))
    (C : NarrowInversionFixedClass (NumberField.RingOfIntegers (Qsqrtd (d : ℚ)))) :
    NarrowClassGroup.mk0 (narrowInversionFixedRepresentativeIdeal d hp0 r hrp0 hrel C) =
      C.1 :=
  (Classical.choose_spec
    (exists_integralIdeal_ramifiedParityRepresentative_of_narrowInversionFixedClass
      d hp0 r hrp0 hrel C)).1

theorem narrowInversionFixedRepresentativeIdeal_mk0_eq_ramifiedParityIdealProduct
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)]
    {p0 : ℕ} (hp0 : p0 ∈ ramifiedPrimes d)
    (r : ({p // p ∈ ramifiedPrimes d} → Fin 2))
    (hrp0 : r ⟨p0, hp0⟩ ≠ 0)
    (hrel : ∀ v : ({p // p ∈ ramifiedPrimes d} → Fin 2),
      NarrowClassGroup.mk0
          (fullRamifiedParityIdealProduct d (fun p => v p + r p)) =
        NarrowClassGroup.mk0 (fullRamifiedParityIdealProduct d v))
    (C : NarrowInversionFixedClass (NumberField.RingOfIntegers (Qsqrtd (d : ℚ)))) :
    NarrowClassGroup.mk0 (narrowInversionFixedRepresentativeIdeal d hp0 r hrp0 hrel C) =
      NarrowClassGroup.mk0
        (ramifiedParityIdealProduct d hp0
          (idealRamifiedParityVector d hp0
            (narrowInversionFixedRepresentativeIdeal d hp0 r hrp0 hrel C))) :=
  (Classical.choose_spec
    (exists_integralIdeal_ramifiedParityRepresentative_of_narrowInversionFixedClass
      d hp0 r hrp0 hrel C)).2

noncomputable def narrowInversionFixedClassRamifiedParityVector
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)]
    {p0 : ℕ} (hp0 : p0 ∈ ramifiedPrimes d)
    (r : ({p // p ∈ ramifiedPrimes d} → Fin 2))
    (hrp0 : r ⟨p0, hp0⟩ ≠ 0)
    (hrel : ∀ v : ({p // p ∈ ramifiedPrimes d} → Fin 2),
      NarrowClassGroup.mk0
          (fullRamifiedParityIdealProduct d (fun p => v p + r p)) =
        NarrowClassGroup.mk0 (fullRamifiedParityIdealProduct d v)) :
    NarrowInversionFixedClass (NumberField.RingOfIntegers (Qsqrtd (d : ℚ))) →
      ({p // p ∈ (ramifiedPrimes d).erase p0} → Fin 2) := by
  classical
  intro C
  exact idealRamifiedParityVector d hp0
    (narrowInversionFixedRepresentativeIdeal d hp0 r hrp0 hrel C)

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
    (hrel : ∀ v : ({p // p ∈ ramifiedPrimes d} → Fin 2),
      NarrowClassGroup.mk0
          (fullRamifiedParityIdealProduct d (fun p => v p + r p)) =
        NarrowClassGroup.mk0 (fullRamifiedParityIdealProduct d v))
    (C : NarrowInversionFixedClass (NumberField.RingOfIntegers (Qsqrtd (d : ℚ)))) :
    ∃ x : (FractionRing (NumberField.RingOfIntegers (Qsqrtd (d : ℚ))))ˣ,
      NarrowClassGroup.IsTotallyPositive
        (x : FractionRing (NumberField.RingOfIntegers (Qsqrtd (d : ℚ)))) ∧
        FractionalIdeal.mk0
            (FractionRing (NumberField.RingOfIntegers (Qsqrtd (d : ℚ))))
            (narrowInversionFixedRepresentativeIdeal d hp0 r hrp0 hrel C) *
          toPrincipalIdeal (NumberField.RingOfIntegers (Qsqrtd (d : ℚ)))
            (FractionRing (NumberField.RingOfIntegers (Qsqrtd (d : ℚ)))) x =
        FractionalIdeal.mk0
          (FractionRing (NumberField.RingOfIntegers (Qsqrtd (d : ℚ))))
          (ramifiedParityIdealProduct d hp0
            (narrowInversionFixedClassRamifiedParityVector d hp0 r hrp0 hrel C)) := by
  have hclass :
      NarrowClassGroup.mk0 (narrowInversionFixedRepresentativeIdeal d hp0 r hrp0 hrel C) =
        NarrowClassGroup.mk0
          (ramifiedParityIdealProduct d hp0
            (narrowInversionFixedClassRamifiedParityVector d hp0 r hrp0 hrel C)) := by
    simpa [narrowInversionFixedClassRamifiedParityVector] using
      narrowInversionFixedRepresentativeIdeal_mk0_eq_ramifiedParityIdealProduct
        d hp0 r hrp0 hrel C
  exact (NarrowClassGroup.mk0_eq_mk0_iff_exists_fraction_ring).mp hclass

/-- If a nonzero strict positive-principal relation among the full ramified
parity vectors is available, then one coordinate can be erased and
inversion-fixed narrow classes inject into the erased parity-vector space. -/
theorem card_narrowInversionFixedClass_le_genusBound_of_positivePrincipal_relation
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)]
    {p0 : ℕ} (hp0 : p0 ∈ ramifiedPrimes d)
    (r : ({p // p ∈ ramifiedPrimes d} → Fin 2))
    (hrp0 : r ⟨p0, hp0⟩ ≠ 0)
    (hrel : ∀ v : ({p // p ∈ ramifiedPrimes d} → Fin 2),
      NarrowClassGroup.mk0
          (fullRamifiedParityIdealProduct d (fun p => v p + r p)) =
        NarrowClassGroup.mk0 (fullRamifiedParityIdealProduct d v)) :
    Nat.card (NarrowInversionFixedClass
      (NumberField.RingOfIntegers (Qsqrtd (d : ℚ)))) ≤
      2 ^ (ramifiedPrimeCount d - 1) := by
  classical
  let R := NumberField.RingOfIntegers (Qsqrtd (d : ℚ))
  let ramifiedParityVector :=
    narrowInversionFixedClassRamifiedParityVector d hp0 r hrp0 hrel
  have hrecoverByRamifiedParity :
      ∀ C : NarrowInversionFixedClass R,
        C.1 = ramifiedParityNarrowClassProduct d hp0 (ramifiedParityVector C) := by
    intro C
    let I := narrowInversionFixedRepresentativeIdeal d hp0 r hrp0 hrel C
    let J := ramifiedParityIdealProduct d hp0 (ramifiedParityVector C)
    have hI_mk0 : NarrowClassGroup.mk0 I = C.1 :=
      narrowInversionFixedRepresentativeIdeal_mk0 d hp0 r hrp0 hrel C
    have hJ_mk0 :
        NarrowClassGroup.mk0 J =
          ramifiedParityNarrowClassProduct d hp0 (ramifiedParityVector C) := by
      simpa [J] using mk0_ramifiedParityIdealProduct d hp0 (ramifiedParityVector C)
    rw [← hI_mk0]
    rw [← hJ_mk0]
    rw [NarrowClassGroup.mk0_eq_mk0_iff_exists_fraction_ring]
    simpa only [I, J, ramifiedParityVector] using
      exists_tp_multiplier_representative_to_ramifiedParityIdealProduct d hp0 r hrp0 hrel C
  let encode : NarrowInversionFixedClass R →
      ({p // p ∈ (ramifiedPrimes d).erase p0} → Fin 2) :=
    ramifiedParityVector
  have hencode_injective : Function.Injective encode := by
    intro C D hCD
    apply Subtype.ext
    rw [hrecoverByRamifiedParity C, hrecoverByRamifiedParity D]
    exact congrArg (ramifiedParityNarrowClassProduct d hp0) hCD
  haveI : Finite (NarrowInversionFixedClass R) :=
    Finite.of_injective encode hencode_injective
  calc
    Nat.card (NarrowInversionFixedClass R) ≤
        Nat.card ({p // p ∈ (ramifiedPrimes d).erase p0} → Fin 2) :=
      Nat.card_le_card_of_injective encode hencode_injective
    _ = 2 ^ (ramifiedPrimeCount d - 1) :=
      card_erasedRamifiedParityVectorDomain d hp0

/-- Remaining positive-principal input in inversion-fixed form: the
inversion-fixed narrow classes are bounded by the genus count. The next
mathematical step is to identify these classes with conjugation-fixed ideal
classes represented by ramified-prime exponent vectors, with the single
positive-principal relation. -/
theorem card_narrowInversionFixedClass_le_genusBound
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] :
    Nat.card (NarrowInversionFixedClass
      (NumberField.RingOfIntegers (Qsqrtd (d : ℚ)))) ≤
      2 ^ (ramifiedPrimeCount d - 1) := by
  classical
  obtain ⟨r, hnonzero, hrel⟩ :=
    exists_nonzero_positivePrincipalRamifiedParityRelation d
  obtain ⟨p0, hrp0⟩ := hnonzero
  exact card_narrowInversionFixedClass_le_genusBound_of_positivePrincipal_relation
    d p0.2 r hrp0 hrel

/-- Ambiguous-ideal upper bound: the two-torsion in the narrow class group has
size at most `2 ^ (t - 1)`, where `t` is the number of ramified rational primes. -/
theorem card_narrowClassGroupTwoTorsion_le_genusBound
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] :
    Nat.card (NarrowClassGroup.twoTorsion
      (NumberField.RingOfIntegers (Qsqrtd (d : ℚ)))) ≤
      2 ^ (ramifiedPrimeCount d - 1) := by
  rw [card_narrowClassGroupTwoTorsion_eq_card_narrowInversionFixedClass]
  exact card_narrowInversionFixedClass_le_genusBound d

/-- Equivalent upper bound for the narrow square-class quotient. -/
theorem card_narrowClassGroupSquareQuotient_le_genusBound
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] :
    Nat.card (Cl⁺(d) ⧸ Subgroup.square (Cl⁺(d))) ≤
      2 ^ (ramifiedPrimeCount d - 1) := by
  rw [card_narrowClassGroupSquareQuotient_eq_card_narrowClassGroupTwoTorsion]
  exact card_narrowClassGroupTwoTorsion_le_genusBound d

end Genus
end ClassGroup
end QuadraticNumberFields
