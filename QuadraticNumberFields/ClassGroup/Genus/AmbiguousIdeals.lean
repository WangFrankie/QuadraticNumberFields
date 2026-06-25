/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/

import QuadraticNumberFields.ClassGroup.Genus.SquareClass
import QuadraticNumberFields.QuadraticField.Conj

/-!
# Ambiguous Ideals

This file records the ambiguous-ideal upper bound for quadratic genus theory.
The proof will identify conjugation-fixed classes with two-torsion classes,
adjust fixed classes to fixed ideals, and then show that only ramified prime
ideals contribute non-principal generators.
-/

namespace QuadraticNumberFields
namespace ClassGroup
namespace Genus

open scoped nonZeroDivisors NumberField QuadraticNumberFields.ClassGroup

attribute [-instance] DivisionRing.toRatAlgebra

/-! ## Ambiguous ideals and quadratic conjugation -/

section FixedIdeals

variable {B : Type*} [CommRing B]

/-- An ideal `I` is ambiguous with respect to a ring automorphism `σ` if `σ`
fixes `I`. -/
def IsAmbiguousIdeal (σ : B ≃+* B) (I : Ideal B) : Prop :=
  Ideal.map (σ : B →+* B) I = I

/-- Ambiguous ideals are exactly fixed points of the induced ideal map. -/
theorem isAmbiguousIdeal_iff_isFixedPt (σ : B ≃+* B) (I : Ideal B) :
    IsAmbiguousIdeal σ I ↔ Function.IsFixedPt (Ideal.map (σ : B →+* B)) I :=
  Iff.rfl

/-- The top ideal is ambiguous. -/
@[simp]
theorem isAmbiguousIdeal_top (σ : B ≃+* B) : IsAmbiguousIdeal σ (⊤ : Ideal B) := by
  rw [IsAmbiguousIdeal, Ideal.map_top]

/-- The product of ambiguous ideals is ambiguous. -/
theorem IsAmbiguousIdeal.mul {σ : B ≃+* B} {I J : Ideal B}
    (hI : IsAmbiguousIdeal σ I) (hJ : IsAmbiguousIdeal σ J) :
    IsAmbiguousIdeal σ (I * J) := by
  unfold IsAmbiguousIdeal at hI hJ ⊢
  rw [Ideal.map_mul, hI, hJ]

end FixedIdeals

/-- The conjugation of a quadratic field `K`, restricted to its ring of integers.
This is the automorphism whose fixed ideals are the ambiguous ideals. -/
noncomputable def conjAutRingOfIntegers (K : Type*) [Field K] [Algebra ℚ K]
    [QuadraticField K] [QuadraticField.Conj K] :
    NumberField.RingOfIntegers K ≃+* NumberField.RingOfIntegers K :=
  NumberField.RingOfIntegers.mapRingEquiv (QuadraticField.conjAut K).toRingEquiv

@[simp]
theorem coe_conjAutRingOfIntegers_apply (K : Type*) [Field K] [Algebra ℚ K]
    [QuadraticField K] [QuadraticField.Conj K] (x : NumberField.RingOfIntegers K) :
    (conjAutRingOfIntegers K x : K) = QuadraticField.conjAut K x := by
  rw [conjAutRingOfIntegers, NumberField.RingOfIntegers.mapRingEquiv_apply]
  rfl

/-! ## Ring-of-integers conjugation API -/

/-- The conjugation of the ring of integers, regarded as a `ℤ`-algebra
automorphism. -/
noncomputable def conjAutRingOfIntegersAlgEquiv (K : Type*) [Field K] [Algebra ℚ K]
    [QuadraticField K] [QuadraticField.Conj K] :
    NumberField.RingOfIntegers K ≃ₐ[ℤ] NumberField.RingOfIntegers K :=
  AlgEquiv.ofRingEquiv (f := conjAutRingOfIntegers K) (by
    intro n
    ext
    rw [coe_conjAutRingOfIntegers_apply]
    simp)

@[simp]
theorem coe_conjAutRingOfIntegersAlgEquiv_apply (K : Type*) [Field K] [Algebra ℚ K]
    [QuadraticField K] [QuadraticField.Conj K] (x : NumberField.RingOfIntegers K) :
    (conjAutRingOfIntegersAlgEquiv K x : K) = QuadraticField.conjAut K x := by
  rw [conjAutRingOfIntegersAlgEquiv]
  exact coe_conjAutRingOfIntegers_apply K x

@[simp]
theorem conjAutRingOfIntegers_apply_apply (K : Type*) [Field K] [Algebra ℚ K]
    [QuadraticField K] [QuadraticField.Conj K] (x : NumberField.RingOfIntegers K) :
    (conjAutRingOfIntegers K) ((conjAutRingOfIntegers K) x) = x := by
  ext
  simpa [coe_conjAutRingOfIntegers_apply] using
    (QuadraticField.Conj.conj_conj (K := K) (x : K))

@[simp]
theorem conjAutRingOfIntegersAlgEquiv_apply_apply (K : Type*) [Field K] [Algebra ℚ K]
    [QuadraticField K] [QuadraticField.Conj K] (x : NumberField.RingOfIntegers K) :
    (conjAutRingOfIntegersAlgEquiv K) ((conjAutRingOfIntegersAlgEquiv K) x) = x := by
  ext
  simpa [coe_conjAutRingOfIntegersAlgEquiv_apply] using
    (QuadraticField.Conj.conj_conj (K := K) (x : K))

private def idealMapMulEquiv {R : Type*} [CommRing R] (σ : R ≃+* R) :
    Ideal R ≃* Ideal R where
  toFun I := Ideal.map (σ : R →+* R) I
  invFun I := Ideal.map (σ.symm : R →+* R) I
  left_inv I := by
    change Ideal.map (σ.symm : R →+* R) (Ideal.map (σ : R →+* R) I) = I
    rw [Ideal.map_map]
    convert Ideal.map_id I
    ext x
    exact σ.symm_apply_apply x
  right_inv I := by
    change Ideal.map (σ : R →+* R) (Ideal.map (σ.symm : R →+* R) I) = I
    rw [Ideal.map_map]
    convert Ideal.map_id I
    ext x
    exact σ.apply_symm_apply x
  map_mul' I J := Ideal.map_mul (σ : R →+* R) I J

/-- The image of a non-zero-divisor ideal under a ring equivalence is again a
non-zero-divisor ideal. -/
private theorem map_ringEquiv_mem_nonZeroDivisors {R : Type*} [CommRing R] (σ : R ≃+* R)
    {I : Ideal R} (hI : I ∈ nonZeroDivisors (Ideal R)) :
    Ideal.map (σ : R →+* R) I ∈ nonZeroDivisors (Ideal R) := by
  rw [← MulEquivClass.map_nonZeroDivisors (idealMapMulEquiv σ)]
  exact ⟨I, hI, rfl⟩

/-- A ring equivalence preserves membership in the Dedekind ideal factorization
multiset. -/
private theorem map_ringEquiv_mem_normalizedFactors_iff {R : Type*}
    [CommRing R] [IsDedekindDomain R] (σ : R ≃+* R) {P I : Ideal R}
    (hI : I ≠ ⊥) :
    Ideal.map (σ : R →+* R) P ∈ UniqueFactorizationMonoid.normalizedFactors
        (Ideal.map (σ : R →+* R) I) ↔
      P ∈ UniqueFactorizationMonoid.normalizedFactors I := by
  have hmapI : Ideal.map (σ : R →+* R) I ≠ ⊥ := by
    intro hbot
    exact hI ((Ideal.map_eq_bot_iff_of_injective
      (f := (σ : R →+* R)) σ.injective).mp hbot)
  rw [Ideal.mem_normalizedFactors_iff hmapI, Ideal.mem_normalizedFactors_iff hI]
  constructor
  · rintro ⟨hPprime, hle⟩
    constructor
    · haveI : (Ideal.map (σ : R →+* R) P).IsPrime := hPprime
      have hPcomap :
          (Ideal.comap (σ : R →+* R) (Ideal.map (σ : R →+* R) P)).IsPrime :=
        inferInstance
      have hP_eq :
          Ideal.comap (σ : R →+* R) (Ideal.map (σ : R →+* R) P) = P :=
        Ideal.comap_map_of_bijective (f := (σ : R →+* R))
          ⟨σ.injective, σ.surjective⟩
      rwa [hP_eq] at hPcomap
    · have hle' : I ≤ Ideal.comap (σ : R →+* R) (Ideal.map (σ : R →+* R) P) :=
        Ideal.map_le_iff_le_comap.mp hle
      have hP_eq :
          Ideal.comap (σ : R →+* R) (Ideal.map (σ : R →+* R) P) = P :=
        Ideal.comap_map_of_bijective (f := (σ : R →+* R))
          ⟨σ.injective, σ.surjective⟩
      rwa [hP_eq] at hle'
  · rintro ⟨hPprime, hle⟩
    haveI : P.IsPrime := hPprime
    exact ⟨Ideal.map_isPrime_of_equiv σ, Ideal.map_mono hle⟩

/-- The conjugate of a nonzero ideal is nonzero, since conjugation is bijective. -/
theorem map_conjAut_mem_nonZeroDivisors (K : Type*) [Field K] [Algebra ℚ K]
    [QuadraticField K] [QuadraticField.Conj K]
    {I : Ideal (NumberField.RingOfIntegers K)}
    (hI : I ∈ nonZeroDivisors (Ideal (NumberField.RingOfIntegers K))) :
    Ideal.map (conjAutRingOfIntegers K : NumberField.RingOfIntegers K →+*
      NumberField.RingOfIntegers K) I ∈
      nonZeroDivisors (Ideal (NumberField.RingOfIntegers K)) :=
  map_ringEquiv_mem_nonZeroDivisors (conjAutRingOfIntegers K) hI

/-- Conjugation preserves membership in the Dedekind ideal factorization
multiset of a nonzero ideal. -/
theorem map_conjAut_mem_normalizedFactors_iff (K : Type*) [Field K] [Algebra ℚ K]
    [QuadraticField K] [QuadraticField.Conj K] [IsDedekindDomain (NumberField.RingOfIntegers K)]
    {P I : Ideal (NumberField.RingOfIntegers K)} (hI : I ≠ ⊥) :
    Ideal.map (conjAutRingOfIntegers K : NumberField.RingOfIntegers K →+*
      NumberField.RingOfIntegers K) P ∈ UniqueFactorizationMonoid.normalizedFactors
        (Ideal.map (conjAutRingOfIntegers K : NumberField.RingOfIntegers K →+*
          NumberField.RingOfIntegers K) I) ↔
      P ∈ UniqueFactorizationMonoid.normalizedFactors I :=
  map_ringEquiv_mem_normalizedFactors_iff (conjAutRingOfIntegers K) hI

/-- For an ambiguous nonzero ideal, conjugation preserves the support of its
Dedekind ideal factorization. -/
theorem map_conjAut_mem_normalizedFactors_iff_of_isAmbiguousIdeal (K : Type*)
    [Field K] [Algebra ℚ K] [QuadraticField K] [QuadraticField.Conj K]
    [IsDedekindDomain (NumberField.RingOfIntegers K)]
    {P I : Ideal (NumberField.RingOfIntegers K)} (hI0 : I ≠ ⊥)
    (hI : IsAmbiguousIdeal (conjAutRingOfIntegers K) I) :
    Ideal.map (conjAutRingOfIntegers K : NumberField.RingOfIntegers K →+*
      NumberField.RingOfIntegers K) P ∈ UniqueFactorizationMonoid.normalizedFactors I ↔
      P ∈ UniqueFactorizationMonoid.normalizedFactors I := by
  rw [IsAmbiguousIdeal] at hI
  simpa [hI] using
    map_conjAut_mem_normalizedFactors_iff (K := K) (P := P) (I := I) hI0

/-- The conjugate of a prime ideal lies over the same rational prime ideal. -/
theorem map_conjAut_liesOver_comap (K : Type*) [Field K] [Algebra ℚ K]
    [QuadraticField K] [QuadraticField.Conj K]
    (P : Ideal (NumberField.RingOfIntegers K)) :
    (Ideal.map (conjAutRingOfIntegers K : NumberField.RingOfIntegers K →+*
      NumberField.RingOfIntegers K) P).LiesOver
        (P.comap (algebraMap ℤ (NumberField.RingOfIntegers K))) := by
  letI : P.LiesOver (P.comap (algebraMap ℤ (NumberField.RingOfIntegers K))) := ⟨rfl⟩
  exact Ideal.LiesOver.of_eq_map_equiv
    (P.comap (algebraMap ℤ (NumberField.RingOfIntegers K)))
    (conjAutRingOfIntegersAlgEquiv K) rfl

/-- The conjugate of a prime ideal is again a prime ideal over the same rational
prime ideal. -/
theorem map_conjAut_mem_primesOver_comap (K : Type*) [Field K] [Algebra ℚ K]
    [QuadraticField K] [QuadraticField.Conj K]
    (P : Ideal (NumberField.RingOfIntegers K)) [P.IsPrime] :
    Ideal.map (conjAutRingOfIntegers K : NumberField.RingOfIntegers K →+*
      NumberField.RingOfIntegers K) P ∈
        Ideal.primesOver (P.comap (algebraMap ℤ (NumberField.RingOfIntegers K)))
          (NumberField.RingOfIntegers K) :=
  ⟨Ideal.map_isPrime_of_equiv (conjAutRingOfIntegers K), map_conjAut_liesOver_comap K P⟩

/-- If the prime ideal above the same rational prime is unique, conjugation fixes
that prime ideal. -/
theorem map_conjAut_eq_of_primesOver_comap_eq_singleton (K : Type*) [Field K] [Algebra ℚ K]
    [QuadraticField K] [QuadraticField.Conj K]
    (P : Ideal (NumberField.RingOfIntegers K)) [P.IsPrime]
    (hsingleton :
      Ideal.primesOver (P.comap (algebraMap ℤ (NumberField.RingOfIntegers K)))
          (NumberField.RingOfIntegers K) =
        {P}) :
    Ideal.map (conjAutRingOfIntegers K : NumberField.RingOfIntegers K →+*
      NumberField.RingOfIntegers K) P = P := by
  have hmem := map_conjAut_mem_primesOver_comap (K := K) P
  rw [hsingleton] at hmem
  simpa using hmem

/-- If `P` is a prime factor of an ambiguous ideal `I`, then its conjugate is
again a prime factor of `I` and lies over the same rational prime ideal as `P`. -/
theorem map_conjAut_mem_normalizedFactors_and_primesOver_comap_of_isAmbiguousIdeal
    (K : Type*) [Field K] [Algebra ℚ K] [QuadraticField K] [QuadraticField.Conj K]
    [IsDedekindDomain (NumberField.RingOfIntegers K)]
    {P I : Ideal (NumberField.RingOfIntegers K)} (hI0 : I ≠ ⊥)
    (hI : IsAmbiguousIdeal (conjAutRingOfIntegers K) I)
    (hP : P ∈ UniqueFactorizationMonoid.normalizedFactors I) :
    Ideal.map (conjAutRingOfIntegers K : NumberField.RingOfIntegers K →+*
        NumberField.RingOfIntegers K) P ∈ UniqueFactorizationMonoid.normalizedFactors I ∧
      Ideal.map (conjAutRingOfIntegers K : NumberField.RingOfIntegers K →+*
        NumberField.RingOfIntegers K) P ∈
          Ideal.primesOver (P.comap (algebraMap ℤ (NumberField.RingOfIntegers K)))
            (NumberField.RingOfIntegers K) := by
  constructor
  · exact (map_conjAut_mem_normalizedFactors_iff_of_isAmbiguousIdeal
      (K := K) (P := P) (I := I) hI0 hI).mpr hP
  · have hPprime : P.IsPrime := (Ideal.mem_normalizedFactors_iff hI0).mp hP |>.1
    haveI : P.IsPrime := hPprime
    exact map_conjAut_mem_primesOver_comap K P

/-- Applying the ring-of-integers conjugation twice fixes every ideal. -/
@[simp]
theorem map_conjAut_map_conjAut (K : Type*) [Field K] [Algebra ℚ K]
    [QuadraticField K] [QuadraticField.Conj K] (I : Ideal (NumberField.RingOfIntegers K)) :
    Ideal.map (conjAutRingOfIntegers K : NumberField.RingOfIntegers K →+*
      NumberField.RingOfIntegers K)
        (Ideal.map (conjAutRingOfIntegers K : NumberField.RingOfIntegers K →+*
          NumberField.RingOfIntegers K) I) = I := by
  rw [Ideal.map_map]
  convert Ideal.map_id I
  ext x
  simp

/-- Conjugation acts multiplicatively on nonzero integral ideals of a quadratic
field. This is the nonzero-ideal action used to formulate ambiguous ideal
representatives. -/
noncomputable def conjAutNonzeroIdealMulEquiv (K : Type*) [Field K] [Algebra ℚ K]
    [QuadraticField K] [QuadraticField.Conj K] :
    (Ideal (NumberField.RingOfIntegers K))⁰ ≃*
      (Ideal (NumberField.RingOfIntegers K))⁰ where
  toFun I :=
    ⟨Ideal.map (conjAutRingOfIntegers K : NumberField.RingOfIntegers K →+*
      NumberField.RingOfIntegers K) I.1, map_conjAut_mem_nonZeroDivisors K I.2⟩
  invFun I :=
    ⟨Ideal.map (conjAutRingOfIntegers K : NumberField.RingOfIntegers K →+*
      NumberField.RingOfIntegers K) I.1, map_conjAut_mem_nonZeroDivisors K I.2⟩
  left_inv I := by
    apply Subtype.ext
    exact map_conjAut_map_conjAut K I.1
  right_inv I := by
    apply Subtype.ext
    exact map_conjAut_map_conjAut K I.1
  map_mul' I J := by
    apply Subtype.ext
    exact Ideal.map_mul (conjAutRingOfIntegers K : NumberField.RingOfIntegers K →+*
      NumberField.RingOfIntegers K) I.1 J.1

@[simp]
theorem coe_conjAutNonzeroIdealMulEquiv_apply (K : Type*) [Field K] [Algebra ℚ K]
    [QuadraticField K] [QuadraticField.Conj K] (I : (Ideal (NumberField.RingOfIntegers K))⁰) :
    ((conjAutNonzeroIdealMulEquiv K I : (Ideal (NumberField.RingOfIntegers K))⁰) :
        Ideal (NumberField.RingOfIntegers K)) =
      Ideal.map (conjAutRingOfIntegers K : NumberField.RingOfIntegers K →+*
        NumberField.RingOfIntegers K) I.1 :=
  rfl

@[simp]
theorem conjAutNonzeroIdealMulEquiv_apply_apply (K : Type*) [Field K] [Algebra ℚ K]
    [QuadraticField K] [QuadraticField.Conj K] (I : (Ideal (NumberField.RingOfIntegers K))⁰) :
    conjAutNonzeroIdealMulEquiv K (conjAutNonzeroIdealMulEquiv K I) = I := by
  apply Subtype.ext
  exact map_conjAut_map_conjAut K I.1

/-- A nonzero integral ideal is ambiguous exactly when it is fixed by the
nonzero-ideal conjugation action. -/
theorem isAmbiguousIdeal_iff_conjAutNonzeroIdealMulEquiv_eq (K : Type*)
    [Field K] [Algebra ℚ K] [QuadraticField K] [QuadraticField.Conj K]
    (I : (Ideal (NumberField.RingOfIntegers K))⁰) :
    IsAmbiguousIdeal (conjAutRingOfIntegers K) I.1 ↔
      conjAutNonzeroIdealMulEquiv K I = I := by
  constructor
  · intro hI
    apply Subtype.ext
    exact hI
  · intro hI
    exact congrArg Subtype.val hI

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

/-- Triviality of a narrow class represented by a nonzero integral ideal is
equivalent to the ideal becoming the inverse of a totally positive principal
fractional ideal. -/
private theorem narrowClassGroup_mk0_eq_one_iff_exists_fraction_ring
    {R : Type*} [CommRing R] [IsDomain R] [IsDedekindDomain R] (I : (Ideal R)⁰) :
    NarrowClassGroup.mk0 I = 1 ↔
      ∃ x : (FractionRing R)ˣ,
        NarrowClassGroup.IsTotallyPositive (x : FractionRing R) ∧
          FractionalIdeal.mk0 (FractionRing R) I *
              toPrincipalIdeal R (FractionRing R) x =
            1 := by
  rw [← map_one (NarrowClassGroup.mk0 : (Ideal R)⁰ →* NarrowClassGroup R)]
  rw [NarrowClassGroup.mk0_eq_mk0_iff_exists_fraction_ring]
  rw [map_one (FractionalIdeal.mk0 (FractionRing R) :
    (Ideal R)⁰ →* (FractionalIdeal R⁰ (FractionRing R))ˣ)]

/-- If a nonzero integral ideal represents an inversion-fixed narrow class, then
its square represents the trivial narrow class. -/
theorem narrowClassGroup_mk0_mul_self_eq_one_of_inversionFixed
    {R : Type*} [CommRing R] [IsDomain R] [IsDedekindDomain R]
    {C : NarrowInversionFixedClass R} {I : (Ideal R)⁰}
    (hI : NarrowClassGroup.mk0 I = C.1) :
    NarrowClassGroup.mk0 (I * I) = 1 := by
  have hmul : (C.1 : NarrowClassGroup R) * C.1 = 1 := by
    nth_rewrite 1 [C.2]
    rw [inv_mul_cancel]
  rw [map_mul, hI]
  exact hmul

/-- An inversion-fixed narrow class has a nonzero integral ideal representative
whose square is cancelled by a totally positive principal fractional ideal. This
is the parity relation used before reducing the representative to ramified
prime exponents. -/
theorem exists_integralIdeal_square_principal_relation_of_narrowInversionFixedClass
    {R : Type*} [CommRing R] [IsDomain R] [IsDedekindDomain R]
    (C : NarrowInversionFixedClass R) :
    ∃ I : (Ideal R)⁰,
      NarrowClassGroup.mk0 I = C.1 ∧
        ∃ x : NarrowClassGroup.totallyPositiveUnits (FractionRing R),
          (FractionalIdeal.mk0 (FractionRing R) I) ^ 2 *
              NarrowClassGroup.toNarrowPrincipalIdeal R (FractionRing R) x =
            1 := by
  obtain ⟨I, hI⟩ := NarrowClassGroup.mk0_surjective C.1
  refine ⟨I, hI, ?_⟩
  have hsq :
      NarrowClassGroup.mk0 (I * I) = (1 : NarrowClassGroup R) :=
    narrowClassGroup_mk0_mul_self_eq_one_of_inversionFixed hI
  obtain ⟨x, hxpos, hx⟩ :=
    (narrowClassGroup_mk0_eq_one_iff_exists_fraction_ring (I * I)).mp hsq
  refine ⟨⟨x, hxpos⟩, ?_⟩
  simpa [pow_two, NarrowClassGroup.toNarrowPrincipalIdeal] using hx

/-- An inversion-fixed narrow class has a nonzero integral ideal representative
whose fractional-ideal square is the inverse of an ordinary principal fractional
ideal generated by a totally positive element. This is the form used by the
factorization step of the ambiguous-ideal bound. -/
theorem exists_integralIdeal_square_eq_principal_inverse_of_narrowInversionFixedClass
    {R : Type*} [CommRing R] [IsDomain R] [IsDedekindDomain R]
    (C : NarrowInversionFixedClass R) :
    ∃ I : (Ideal R)⁰,
      NarrowClassGroup.mk0 I = C.1 ∧
        ∃ x : (FractionRing R)ˣ,
          NarrowClassGroup.IsTotallyPositive (x : FractionRing R) ∧
            (FractionalIdeal.mk0 (FractionRing R) I) ^ 2 =
              (toPrincipalIdeal R (FractionRing R) x)⁻¹ := by
  obtain ⟨I, hI, x, hx⟩ :=
    exists_integralIdeal_square_principal_relation_of_narrowInversionFixedClass C
  refine ⟨I, hI, x.1, x.2, ?_⟩
  refine (eq_inv_iff_mul_eq_one).2 ?_
  simpa [NarrowClassGroup.toNarrowPrincipalIdeal] using hx

/-- Remaining ambiguous-class-number input in inversion-fixed form: the
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
  let R := NumberField.RingOfIntegers (Qsqrtd (d : ℚ))
  have hrel :
      ∀ C : NarrowInversionFixedClass R,
        ∃ I : (Ideal R)⁰,
          NarrowClassGroup.mk0 I = C.1 ∧
            ∃ x : (FractionRing R)ˣ,
              NarrowClassGroup.IsTotallyPositive (x : FractionRing R) ∧
                (FractionalIdeal.mk0 (FractionRing R) I) ^ 2 =
                  (toPrincipalIdeal R (FractionRing R) x)⁻¹ := by
    intro C
    exact exists_integralIdeal_square_eq_principal_inverse_of_narrowInversionFixedClass C
  have hconj :
      ∀ I : (Ideal R)⁰,
        conjAutNonzeroIdealMulEquiv (Qsqrtd (d : ℚ))
            (conjAutNonzeroIdealMulEquiv (Qsqrtd (d : ℚ)) I) = I := by
    intro I
    exact conjAutNonzeroIdealMulEquiv_apply_apply (Qsqrtd (d : ℚ)) I
  have hambiguousFixed :
      ∀ I : (Ideal R)⁰,
        IsAmbiguousIdeal (conjAutRingOfIntegers (Qsqrtd (d : ℚ))) I.1 ↔
          conjAutNonzeroIdealMulEquiv (Qsqrtd (d : ℚ)) I = I := by
    intro I
    exact isAmbiguousIdeal_iff_conjAutNonzeroIdealMulEquiv_eq (Qsqrtd (d : ℚ)) I
  have hconjFactors :
      ∀ {P I : Ideal R}, I ≠ ⊥ →
        (Ideal.map (conjAutRingOfIntegers (Qsqrtd (d : ℚ)) : R →+* R) P ∈
            UniqueFactorizationMonoid.normalizedFactors
              (Ideal.map (conjAutRingOfIntegers (Qsqrtd (d : ℚ)) : R →+* R) I) ↔
          P ∈ UniqueFactorizationMonoid.normalizedFactors I) := by
    intro P I
    exact fun hI =>
      map_conjAut_mem_normalizedFactors_iff (K := Qsqrtd (d : ℚ)) (P := P) (I := I) hI
  have hambiguousFactors :
      ∀ {P : Ideal R} {I : (Ideal R)⁰},
        IsAmbiguousIdeal (conjAutRingOfIntegers (Qsqrtd (d : ℚ))) I.1 →
          (Ideal.map (conjAutRingOfIntegers (Qsqrtd (d : ℚ)) : R →+* R) P ∈
              UniqueFactorizationMonoid.normalizedFactors I.1 ↔
            P ∈ UniqueFactorizationMonoid.normalizedFactors I.1) := by
    intro P I hI
    have hI0 : I.1 ≠ ⊥ := by
      rw [← Ideal.zero_eq_bot]
      exact mem_nonZeroDivisors_iff_ne_zero.mp I.2
    exact map_conjAut_mem_normalizedFactors_iff_of_isAmbiguousIdeal
      (K := Qsqrtd (d : ℚ)) (P := P) (I := I.1) hI0 hI
  have hconjPrimesOver :
      ∀ {P : Ideal R}, P.IsPrime →
        Ideal.map (conjAutRingOfIntegers (Qsqrtd (d : ℚ)) : R →+* R) P ∈
          Ideal.primesOver (P.comap (algebraMap ℤ R)) R := by
    intro P hP
    haveI : P.IsPrime := hP
    exact map_conjAut_mem_primesOver_comap (K := Qsqrtd (d : ℚ)) P
  have hconjFixedOfSingleton :
      ∀ {P : Ideal R}, P.IsPrime →
        Ideal.primesOver (P.comap (algebraMap ℤ R)) R = {P} →
          Ideal.map (conjAutRingOfIntegers (Qsqrtd (d : ℚ)) : R →+* R) P = P := by
    intro P hP hsingleton
    haveI : P.IsPrime := hP
    exact map_conjAut_eq_of_primesOver_comap_eq_singleton
      (K := Qsqrtd (d : ℚ)) P hsingleton
  have hambiguousPrimeFactorConj :
      ∀ {P : Ideal R} {I : (Ideal R)⁰},
        IsAmbiguousIdeal (conjAutRingOfIntegers (Qsqrtd (d : ℚ))) I.1 →
          P ∈ UniqueFactorizationMonoid.normalizedFactors I.1 →
            Ideal.map (conjAutRingOfIntegers (Qsqrtd (d : ℚ)) : R →+* R) P ∈
                UniqueFactorizationMonoid.normalizedFactors I.1 ∧
              Ideal.map (conjAutRingOfIntegers (Qsqrtd (d : ℚ)) : R →+* R) P ∈
                Ideal.primesOver (P.comap (algebraMap ℤ R)) R := by
    intro P I hI hP
    have hI0 : I.1 ≠ ⊥ := by
      rw [← Ideal.zero_eq_bot]
      exact mem_nonZeroDivisors_iff_ne_zero.mp I.2
    exact map_conjAut_mem_normalizedFactors_and_primesOver_comap_of_isAmbiguousIdeal
      (K := Qsqrtd (d : ℚ)) (P := P) (I := I.1) hI0 hI hP
  sorry

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
