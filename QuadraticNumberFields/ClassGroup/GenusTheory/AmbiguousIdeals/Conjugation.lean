/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/

import Mathlib.RepresentationTheory.Homological.GroupCohomology.Hilbert90
import Mathlib.RingTheory.Ideal.Norm.RelNorm
import QNFMathlib.NumberTheory.NumberField.Galois
import QNFMathlib.RingTheory.FractionalIdeal.RingEquiv
import QNFMathlib.RingTheory.Ideal.Norm.AbsNorm
import QuadraticNumberFields.ClassGroup.GenusTheory.SquareClass
import QuadraticNumberFields.QuadraticField.Conj
import QuadraticNumberFields.RingOfIntegers.Norm
import QuadraticNumberFields.Splitting.Factorization

/-!
# Ambiguous Ideals

This file records the ambiguous-ideal upper bound for quadratic genus theory.
The proof will identify conjugation-fixed classes with two-torsion classes,
adjust fixed classes to fixed ideals, and then show that only ramified prime
ideals contribute non-principal generators.
-/

namespace QuadraticNumberFields
namespace ClassGroup
namespace GenusTheory

open scoped nonZeroDivisors NumberField Pointwise QuadraticNumberFields.ClassGroup
open scoped QuadraticNumberFields.Splitting

attribute [-instance] DivisionRing.toRatAlgebra
attribute [local instance] FractionRing.liftAlgebra

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

/-- Restricting field conjugation to the ring of integers gives the
`ℤ`-algebra automorphism `conjAutRingOfIntegersAlgEquiv`. -/
theorem galRestrict_conjAut_eq_conjAutRingOfIntegers (K : Type*) [Field K] [NumberField K]
    [Algebra ℚ K] [QuadraticField K] [QuadraticField.Conj K] :
    galRestrict ℤ ℚ K (NumberField.RingOfIntegers K) (QuadraticField.conjAut K) =
      conjAutRingOfIntegersAlgEquiv K := by
  ext x
  simpa [conjAutRingOfIntegersAlgEquiv, coe_conjAutRingOfIntegers_apply] using
    (algebraMap_galRestrict_apply (A := ℤ) (K := ℚ) (L := K)
      (B := NumberField.RingOfIntegers K) (QuadraticField.conjAut K) x)

/-- The induced `ℤ`-algebra conjugation on the ring of integers is nontrivial. -/
theorem conjAutRingOfIntegersAlgEquiv_ne_refl (K : Type*) [Field K] [NumberField K]
    [Algebra ℚ K] [QuadraticField K] [QuadraticField.Conj K] :
    conjAutRingOfIntegersAlgEquiv K ≠ AlgEquiv.refl := by
  intro h
  apply QuadraticField.Conj.conj_ne_refl (K := K)
  apply (galRestrict ℤ ℚ K (NumberField.RingOfIntegers K)).injective
  rw [galRestrict_conjAut_eq_conjAutRingOfIntegers K, h]
  change (1 : NumberField.RingOfIntegers K ≃ₐ[ℤ] NumberField.RingOfIntegers K) =
    (galRestrict ℤ ℚ K (NumberField.RingOfIntegers K)) (1 : Gal(K / ℚ))
  rw [map_one]

/-- Quadratic conjugation on the fraction field of the ring of integers, obtained
by localizing the ring-of-integers conjugation. -/
noncomputable def conjAutFractionRingAlgEquiv
    (K : Type*) [Field K] [NumberField K] [Algebra ℚ K]
    [QuadraticField K] [QuadraticField.Conj K] :
    FractionRing (NumberField.RingOfIntegers K) ≃ₐ[ℤ]
      FractionRing (NumberField.RingOfIntegers K) :=
  IsFractionRing.algEquivOfAlgEquiv (conjAutRingOfIntegersAlgEquiv K)

@[simp]
theorem conjAutFractionRingAlgEquiv_algebraMap
    (K : Type*) [Field K] [NumberField K] [Algebra ℚ K]
    [QuadraticField K] [QuadraticField.Conj K]
    (x : NumberField.RingOfIntegers K) :
    conjAutFractionRingAlgEquiv K
        (algebraMap (NumberField.RingOfIntegers K)
          (FractionRing (NumberField.RingOfIntegers K)) x) =
      algebraMap (NumberField.RingOfIntegers K)
        (FractionRing (NumberField.RingOfIntegers K))
        ((conjAutRingOfIntegers K) x) := by
  simp [conjAutFractionRingAlgEquiv, conjAutRingOfIntegersAlgEquiv]

@[simp]
theorem fractionRing_algEquiv_conjAutFractionRingAlgEquiv
    (K : Type*) [Field K] [NumberField K] [Algebra ℚ K]
    [QuadraticField K] [QuadraticField.Conj K]
    (z : FractionRing (NumberField.RingOfIntegers K)) :
    FractionRing.algEquiv (NumberField.RingOfIntegers K) K
        ((conjAutFractionRingAlgEquiv K) z) =
      QuadraticField.conjAut K
        (FractionRing.algEquiv (NumberField.RingOfIntegers K) K z) := by
  let R := NumberField.RingOfIntegers K
  have hhom :
      ((FractionRing.algEquiv R K).toRingHom.comp
          (conjAutFractionRingAlgEquiv K).toRingHom) =
        ((QuadraticField.conjAut K).toRingHom.comp
          (FractionRing.algEquiv R K).toRingHom) := by
    apply IsFractionRing.ringHom_ext (A := R) (K := FractionRing R) (L := K)
    intro x
    simp [R, RingHom.comp_apply, coe_conjAutRingOfIntegers_apply]
  exact RingHom.congr_fun hhom z

/-- Hilbert 90 in the form used for quadratic integer rings: a norm-one
integer-ring element is a conjugation coboundary. -/
theorem exists_mul_conjAutRingOfIntegers_eq_self_of_norm_eq_one
    (K : Type) [Field K] [NumberField K] [Algebra ℚ K]
    [QuadraticField K] [QuadraticField.Conj K]
    {η : NumberField.RingOfIntegers K}
    (hη : Algebra.norm ℚ (η : K) = 1) :
    ∃ ε : NumberField.RingOfIntegers K, ε ≠ 0 ∧
      η * (conjAutRingOfIntegers K) ε = ε := by
  haveI : IsGalois ℚ K := Algebra.IsQuadraticExtension.isGalois ℚ K
  have hcard : Nat.card Gal(K / ℚ) = 2 := by
    rw [IsGalois.card_aut_eq_finrank, Algebra.IsQuadraticExtension.finrank_eq_two]
  haveI : IsCyclic Gal(K / ℚ) := isCyclic_of_prime_card hcard
  have hconj_ne_one : (QuadraticField.conjAut K : Gal(K / ℚ)) ≠ 1 := by
    simpa using (QuadraticField.Conj.conj_ne_refl (K := K))
  have hg : ∀ σ : Gal(K / ℚ), σ ∈ Subgroup.zpowers (QuadraticField.conjAut K) := by
    intro σ
    exact mem_zpowers_of_prime_card (p := 2) hcard hconj_ne_one
  obtain ⟨ε, hε0, hε⟩ :=
    groupCohomology.exists_mul_galRestrict_of_norm_eq_one
      (A := ℤ) (K := ℚ) (L := K) (B := NumberField.RingOfIntegers K)
      (g := QuadraticField.conjAut K) hg (by simpa using hη)
  refine ⟨ε, hε0, ?_⟩
  simpa [galRestrict_conjAut_eq_conjAutRingOfIntegers K] using hε

/-- The fraction-field extension attached to the ring of integers of a quadratic
number field has degree two. -/
theorem finrank_fractionRing_ringOfIntegers_eq_two (K : Type*) [Field K] [NumberField K]
    [Algebra ℚ K] [QuadraticField K] :
    Module.finrank (FractionRing ℤ) (FractionRing (NumberField.RingOfIntegers K)) = 2 := by
  haveI : Algebra.IsAlgebraic ℤ (NumberField.RingOfIntegers K) :=
    Algebra.IsAlgebraic.of_finite ℤ (NumberField.RingOfIntegers K)
  calc
    Module.finrank (FractionRing ℤ) (FractionRing (NumberField.RingOfIntegers K)) =
        Module.finrank ℤ (NumberField.RingOfIntegers K) := by
      simpa using
        (Algebra.IsAlgebraic.finrank_of_isFractionRing (R := ℤ) (R' := FractionRing ℤ)
          (S := NumberField.RingOfIntegers K)
          (S' := FractionRing (NumberField.RingOfIntegers K)))
    _ = Module.finrank ℚ K := by
      convert NumberField.RingOfIntegers.rank (K := K)
      exact Subsingleton.elim _ _
    _ = 2 := Algebra.IsQuadraticExtension.finrank_eq_two ℚ K

/-- The Galois group of the fraction-field extension attached to `𝓞 K / ℤ` has
two elements for a quadratic number field. -/
theorem card_gal_fractionRing_ringOfIntegers_eq_two (K : Type*) [Field K] [NumberField K]
    [Algebra ℚ K] [QuadraticField K] :
    Nat.card Gal(FractionRing (NumberField.RingOfIntegers K) / FractionRing ℤ) = 2 := by
  haveI : IsGalois ℚ K := Algebra.IsQuadraticExtension.isGalois ℚ K
  haveI : IsGalois (FractionRing ℤ) (FractionRing (NumberField.RingOfIntegers K)) :=
    NumberField.isGalois_fractionRing_ringOfIntegers K
  rw [IsGalois.card_aut_eq_finrank]
  exact finrank_fractionRing_ringOfIntegers_eq_two K

/-- For a nonzero prime ideal `P` of `𝓞 K`, its relative ideal norm over `ℤ` is
the prime below `P`, raised to the inertia degree. -/
theorem relNorm_eq_comap_pow_inertiaDeg_of_isPrime (K : Type*) [Field K] [NumberField K]
    [Algebra ℚ K] [QuadraticField K]
    (P : Ideal (NumberField.RingOfIntegers K)) [P.IsPrime] (hP0 : P ≠ ⊥) :
    Ideal.relNorm ℤ P =
      (P.comap (algebraMap ℤ (NumberField.RingOfIntegers K))) ^
        (P.comap (algebraMap ℤ (NumberField.RingOfIntegers K))).inertiaDeg P := by
  haveI : IsGalois ℚ K := Algebra.IsQuadraticExtension.isGalois ℚ K
  haveI : IsGalois (FractionRing ℤ) (FractionRing (NumberField.RingOfIntegers K)) :=
    NumberField.isGalois_fractionRing_ringOfIntegers K
  haveI : P.IsMaximal := Ideal.IsPrime.isMaximal inferInstance hP0
  haveI : (P.comap (algebraMap ℤ (NumberField.RingOfIntegers K))).IsMaximal :=
    Ideal.isMaximal_comap_of_isIntegral_of_isMaximal P
  exact Ideal.relNorm_eq_pow_of_isPrime_isGalois P
    (P.comap (algebraMap ℤ (NumberField.RingOfIntegers K)))

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

def idealMapMulEquiv {R : Type*} [CommRing R] (σ : R ≃+* R) :
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
theorem map_ringEquiv_mem_nonZeroDivisors {R : Type*} [CommRing R] (σ : R ≃+* R)
    {I : Ideal R} (hI : I ∈ nonZeroDivisors (Ideal R)) :
    Ideal.map (σ : R →+* R) I ∈ nonZeroDivisors (Ideal R) := by
  rw [← MulEquivClass.map_nonZeroDivisors (idealMapMulEquiv σ)]
  exact ⟨I, hI, rfl⟩

/-- Mapping ideals by a ring equivalence is injective. -/
theorem ideal_map_ringEquiv_injective {R : Type*} [CommRing R] (σ : R ≃+* R) :
    Function.Injective (fun P : Ideal R => Ideal.map (σ : R →+* R) P) := by
  intro P Q hPQ
  change Ideal.map (σ : R →+* R) P = Ideal.map (σ : R →+* R) Q at hPQ
  have hP : Ideal.comap (σ : R →+* R) (Ideal.map (σ : R →+* R) P) = P :=
    Ideal.comap_map_of_bijective (f := (σ : R →+* R)) ⟨σ.injective, σ.surjective⟩
  have hQ : Ideal.comap (σ : R →+* R) (Ideal.map (σ : R →+* R) Q) = Q :=
    Ideal.comap_map_of_bijective (f := (σ : R →+* R)) ⟨σ.injective, σ.surjective⟩
  rw [← hP, hPQ, hQ]

/-- Mapping a multiset product of ideals by a ring equivalence maps each factor. -/
theorem ideal_map_ringEquiv_multiset_prod {R : Type*} [CommRing R]
    (σ : R ≃+* R) (s : Multiset (Ideal R)) :
    Ideal.map (σ : R →+* R) s.prod =
      (s.map fun P => Ideal.map (σ : R →+* R) P).prod := by
  induction s using Multiset.induction_on with
  | empty =>
      rw [Multiset.prod_zero, Multiset.map_zero, Multiset.prod_zero,
        Ideal.one_eq_top, Ideal.map_top]
  | cons P s ih => simp [Ideal.map_mul, ih]

/-- A ring equivalence maps the normalized factorization multiset of a nonzero
Dedekind ideal to the normalized factorization multiset of its image. -/
theorem normalizedFactors_map_ringEquiv {R : Type*}
    [CommRing R] [IsDedekindDomain R] (σ : R ≃+* R)
    {I : Ideal R} (hI : I ≠ ⊥) :
    UniqueFactorizationMonoid.normalizedFactors (Ideal.map (σ : R →+* R) I) =
      (UniqueFactorizationMonoid.normalizedFactors I).map
        (fun P => Ideal.map (σ : R →+* R) P) := by
  classical
  have hprod : Ideal.map (σ : R →+* R) I =
      ((UniqueFactorizationMonoid.normalizedFactors I).map
        (fun P => Ideal.map (σ : R →+* R) P)).prod := by
    calc
      Ideal.map (σ : R →+* R) I =
          Ideal.map (σ : R →+* R)
            (UniqueFactorizationMonoid.normalizedFactors I).prod := by
        rw [Ideal.prod_normalizedFactors_eq_self hI]
      _ = ((UniqueFactorizationMonoid.normalizedFactors I).map
          (fun P => Ideal.map (σ : R →+* R) P)).prod := by
        exact ideal_map_ringEquiv_multiset_prod σ _
  rw [hprod]
  apply UniqueFactorizationMonoid.normalizedFactors_prod_of_prime
  intro Q hQ
  rcases Multiset.mem_map.mp hQ with ⟨P, hP, rfl⟩
  have hPdata := (Ideal.mem_normalizedFactors_iff hI).mp hP
  have hPprime : P.IsPrime := hPdata.1
  have hPle : I ≤ P := hPdata.2
  have hP0 : P ≠ ⊥ := by
    intro hPbot
    exact hI (le_bot_iff.mp (by simpa [hPbot] using hPle))
  have hmapP0 : Ideal.map (σ : R →+* R) P ≠ ⊥ := by
    intro hbot
    exact hP0 ((Ideal.map_eq_bot_iff_of_injective
      (f := (σ : R →+* R)) σ.injective).mp hbot)
  exact (Ideal.prime_iff_isPrime hmapP0).mpr (Ideal.map_isPrime_of_equiv σ)

/-- A ring equivalence preserves normalized-factor multiplicities after applying
the equivalence to the counted factor. -/
theorem normalizedFactors_count_map_ringEquiv {R : Type*}
    [CommRing R] [IsDedekindDomain R] (σ : R ≃+* R)
    {P I : Ideal R} (hI : I ≠ ⊥) :
    (UniqueFactorizationMonoid.normalizedFactors (Ideal.map (σ : R →+* R) I)).count
        (Ideal.map (σ : R →+* R) P) =
      (UniqueFactorizationMonoid.normalizedFactors I).count P := by
  rw [normalizedFactors_map_ringEquiv σ hI]
  rw [Multiset.count_map_eq_count' _ _ (ideal_map_ringEquiv_injective σ) P]

/-- A ring equivalence preserves membership in the Dedekind ideal factorization
multiset. -/
theorem map_ringEquiv_mem_normalizedFactors_iff {R : Type*}
    [CommRing R] [IsDedekindDomain R] (σ : R ≃+* R) {P I : Ideal R}
    (hI : I ≠ ⊥) :
    Ideal.map (σ : R →+* R) P ∈ UniqueFactorizationMonoid.normalizedFactors
        (Ideal.map (σ : R →+* R) I) ↔
      P ∈ UniqueFactorizationMonoid.normalizedFactors I := by
  constructor
  · intro h
    rw [← Multiset.count_pos] at h ⊢
    rwa [← normalizedFactors_count_map_ringEquiv σ hI]
  · intro h
    rw [← Multiset.count_pos] at h ⊢
    rwa [normalizedFactors_count_map_ringEquiv σ hI]

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

/-- For an ambiguous nonzero ideal, conjugation preserves normalized-factor
multiplicity. -/
theorem map_conjAut_count_normalizedFactors_eq_of_isAmbiguousIdeal (K : Type*)
    [Field K] [Algebra ℚ K] [QuadraticField K] [QuadraticField.Conj K]
    [IsDedekindDomain (NumberField.RingOfIntegers K)]
    {P I : Ideal (NumberField.RingOfIntegers K)} (hI0 : I ≠ ⊥)
    (hI : IsAmbiguousIdeal (conjAutRingOfIntegers K) I) :
    (UniqueFactorizationMonoid.normalizedFactors I).count
        (Ideal.map (conjAutRingOfIntegers K :
          NumberField.RingOfIntegers K →+* NumberField.RingOfIntegers K) P) =
      (UniqueFactorizationMonoid.normalizedFactors I).count P := by
  rw [IsAmbiguousIdeal] at hI
  simpa [hI] using
    normalizedFactors_count_map_ringEquiv
      (conjAutRingOfIntegers K) (P := P) (I := I) hI0

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
  have hcount :=
    map_conjAut_count_normalizedFactors_eq_of_isAmbiguousIdeal
      (K := K) (P := P) (I := I) hI0 hI
  constructor
  · intro h
    rw [← Multiset.count_pos] at h ⊢
    rwa [hcount] at h
  · intro h
    rw [← Multiset.count_pos] at h ⊢
    rwa [hcount]

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

/-- In a quadratic Dedekind extension, a ramified prime has a singleton fiber
above it. -/
theorem exists_primesOver_eq_singleton_of_isRamifiedIn
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [Nontrivial R] [IsDedekindDomain R] [IsDedekindDomain S]
    [Algebra.IsQuadraticExtension R S]
    {p : Ideal R} (hchar : ringChar R ≠ 2) (hp : p ≠ ⊥) [p.IsMaximal]
    (hr : Ideal.IsRamifiedIn p S) :
    ∃ P : Ideal S, Ideal.primesOver p S = {P} := by
  have hg : (Ideal.primesOver p S).ncard = 1 :=
    ((Ideal.one_lt_ramificationIdxIn_iff_efg p S hchar hp).mp hr).1
  rw [Set.ncard_eq_one] at hg
  exact hg

/-- In a quadratic Dedekind extension, a ramified prime has a unique prime above it. -/
theorem primesOver_eq_singleton_of_isRamifiedIn
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [Nontrivial R] [IsDedekindDomain R] [IsDedekindDomain S]
    [Algebra.IsQuadraticExtension R S]
    {p : Ideal R} (hchar : ringChar R ≠ 2) (hp : p ≠ ⊥) [p.IsMaximal]
    {P : Ideal S} (hP : P ∈ Ideal.primesOver p S)
    (hr : Ideal.IsRamifiedIn p S) :
    Ideal.primesOver p S = {P} := by
  obtain ⟨Q, hQ⟩ :=
    exists_primesOver_eq_singleton_of_isRamifiedIn
      (S := S) (p := p) hchar hp hr
  have hPQ : P = Q := by
    rw [hQ] at hP
    exact hP
  simpa [hPQ] using hQ

/-- A prime ideal over a ramified rational prime in `ℚ(√d)` is fixed by
quadratic conjugation. -/
theorem map_conjAut_eq_of_mem_primesOver_of_isRamifiedIn
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] {p : ℕ} [Fact p.Prime]
    {P : Ideal (NumberField.RingOfIntegers (Qsqrtd (d : ℚ)))}
    (hP : P ∈ Ideal.primesOver (𝔭(p))
      (NumberField.RingOfIntegers (Qsqrtd (d : ℚ))))
    (hr : Ideal.IsRamifiedIn (𝔭(p))
      (NumberField.RingOfIntegers (Qsqrtd (d : ℚ)))) :
    Ideal.map (conjAutRingOfIntegers (Qsqrtd (d : ℚ)) :
      NumberField.RingOfIntegers (Qsqrtd (d : ℚ)) →+*
        NumberField.RingOfIntegers (Qsqrtd (d : ℚ))) P = P := by
  have hp0 : (𝔭(p) : Ideal ℤ) ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot, Nat.cast_eq_zero]
    exact (Fact.out : Nat.Prime p).ne_zero
  haveI : (𝔭(p) : Ideal ℤ).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible
      ((Nat.prime_iff_prime_int.mp (Fact.out : Nat.Prime p)).irreducible)
  have hsingletonBase :
      Ideal.primesOver (𝔭(p)) (NumberField.RingOfIntegers (Qsqrtd (d : ℚ))) = {P} :=
    primesOver_eq_singleton_of_isRamifiedIn
      (S := NumberField.RingOfIntegers (Qsqrtd (d : ℚ))) (p := 𝔭(p))
      (by simp [ringChar.eq_zero]) hp0 hP hr
  have hPprime : P.IsPrime := hP.1
  haveI : P.IsPrime := hPprime
  letI : P.LiesOver (𝔭(p)) := hP.2
  have hsingletonComap :
      Ideal.primesOver
          (P.comap (algebraMap ℤ (NumberField.RingOfIntegers (Qsqrtd (d : ℚ)))))
          (NumberField.RingOfIntegers (Qsqrtd (d : ℚ))) = {P} := by
    change Ideal.primesOver (P.under ℤ)
      (NumberField.RingOfIntegers (Qsqrtd (d : ℚ))) = {P}
    rw [← Ideal.LiesOver.over (p := 𝔭(p)) (P := P)]
    exact hsingletonBase
  exact map_conjAut_eq_of_primesOver_comap_eq_singleton
    (K := Qsqrtd (d : ℚ)) P hsingletonComap

/-- A rational prime from `ramifiedPrimes d` has a singleton prime-ideal fiber
in the ring of integers of `ℚ(√d)`. -/
theorem exists_primesOver_eq_singleton_of_mem_ramifiedPrimes
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)]
    {p : ℕ} (hp : p ∈ ramifiedPrimes d) :
    ∃ P : Ideal (NumberField.RingOfIntegers (Qsqrtd (d : ℚ))),
      Ideal.primesOver (𝔭(p)) (NumberField.RingOfIntegers (Qsqrtd (d : ℚ))) = {P} := by
  have hpPrime : p.Prime := prime_of_mem_ramifiedPrimes hp
  letI : Fact p.Prime := ⟨hpPrime⟩
  have hp0 : (𝔭(p) : Ideal ℤ) ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot, Nat.cast_eq_zero]
    exact hpPrime.ne_zero
  haveI : (𝔭(p) : Ideal ℤ).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible
      ((Nat.prime_iff_prime_int.mp hpPrime).irreducible)
  have hram : Ideal.IsRamifiedIn (𝔭(p))
      (NumberField.RingOfIntegers (Qsqrtd (d : ℚ))) :=
    ((mem_ramifiedPrimes_iff_isRamifiedIn d p).mp hp).2
  exact exists_primesOver_eq_singleton_of_isRamifiedIn
    (S := NumberField.RingOfIntegers (Qsqrtd (d : ℚ))) (p := 𝔭(p))
    (by simp [ringChar.eq_zero]) hp0 hram

/-- If `P` lies over a rational prime from `ramifiedPrimes d`, then that fiber
is exactly `{P}`. -/
theorem primesOver_eq_singleton_of_mem_ramifiedPrimes
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)]
    {p : ℕ} (hp : p ∈ ramifiedPrimes d)
    {P : Ideal (NumberField.RingOfIntegers (Qsqrtd (d : ℚ)))}
    (hP : P ∈ Ideal.primesOver (𝔭(p))
      (NumberField.RingOfIntegers (Qsqrtd (d : ℚ)))) :
    Ideal.primesOver (𝔭(p)) (NumberField.RingOfIntegers (Qsqrtd (d : ℚ))) = {P} := by
  obtain ⟨Q, hQ⟩ := exists_primesOver_eq_singleton_of_mem_ramifiedPrimes (d := d) hp
  have hPQ : P = Q := by
    rw [hQ] at hP
    exact hP
  simpa [hPQ] using hQ

noncomputable def ramifiedPrimeIdeal
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)]
    {p : ℕ} (hp : p ∈ ramifiedPrimes d) :
    Ideal (NumberField.RingOfIntegers (Qsqrtd (d : ℚ))) :=
  (exists_primesOver_eq_singleton_of_mem_ramifiedPrimes (d := d) hp).choose

theorem primesOver_eq_singleton_ramifiedPrimeIdeal
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)]
    {p : ℕ} (hp : p ∈ ramifiedPrimes d) :
    Ideal.primesOver (𝔭(p)) (NumberField.RingOfIntegers (Qsqrtd (d : ℚ))) =
      {ramifiedPrimeIdeal d hp} :=
  (exists_primesOver_eq_singleton_of_mem_ramifiedPrimes (d := d) hp).choose_spec

theorem ramifiedPrimeIdeal_mem_primesOver
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)]
    {p : ℕ} (hp : p ∈ ramifiedPrimes d) :
    ramifiedPrimeIdeal d hp ∈
      Ideal.primesOver (𝔭(p)) (NumberField.RingOfIntegers (Qsqrtd (d : ℚ))) := by
  rw [primesOver_eq_singleton_ramifiedPrimeIdeal]
  exact Set.mem_singleton _

theorem ramifiedPrimeIdeal_ne_bot
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)]
    {p : ℕ} (hp : p ∈ ramifiedPrimes d) :
    ramifiedPrimeIdeal d hp ≠ ⊥ := by
  have hpPrime : p.Prime := prime_of_mem_ramifiedPrimes hp
  have hp0 : (𝔭(p) : Ideal ℤ) ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot, Nat.cast_eq_zero]
    exact hpPrime.ne_zero
  exact Ideal.ne_bot_of_mem_primesOver hp0 (ramifiedPrimeIdeal_mem_primesOver d hp)

/-- The distinguished ramified prime ideal remembers the rational prime below
it. -/
theorem ramifiedPrimeIdeal_eq_iff
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)]
    {p q : ℕ} (hp : p ∈ ramifiedPrimes d) (hq : q ∈ ramifiedPrimes d) :
    ramifiedPrimeIdeal d hp = ramifiedPrimeIdeal d hq ↔ p = q := by
  constructor
  · intro h
    have hp_under :=
      (ramifiedPrimeIdeal_mem_primesOver d hp).2.1
    have hq_under :=
      (ramifiedPrimeIdeal_mem_primesOver d hq).2.1
    have hspan :
        (𝔭(p) : Ideal ℤ) = 𝔭(q) := by
      rw [hp_under, hq_under, h]
    have hassoc :
        Associated (p : ℤ) (q : ℤ) :=
      Ideal.span_singleton_eq_span_singleton.mp hspan
    exact_mod_cast (Int.associated_iff_natAbs.mp hassoc)
  · rintro rfl
    rfl

/-- A prime ideal over a rational prime from the genus-theory ramified-prime set
is fixed by quadratic conjugation. -/
theorem map_conjAut_eq_of_mem_primesOver_of_mem_ramifiedPrimes
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)]
    {p : ℕ} (hp : p ∈ ramifiedPrimes d)
    {P : Ideal (NumberField.RingOfIntegers (Qsqrtd (d : ℚ)))}
    (hP : P ∈ Ideal.primesOver (𝔭(p))
      (NumberField.RingOfIntegers (Qsqrtd (d : ℚ)))) :
    Ideal.map (conjAutRingOfIntegers (Qsqrtd (d : ℚ)) :
      NumberField.RingOfIntegers (Qsqrtd (d : ℚ)) →+*
      NumberField.RingOfIntegers (Qsqrtd (d : ℚ))) P = P := by
  have hpPrime : p.Prime := prime_of_mem_ramifiedPrimes hp
  letI : Fact p.Prime := ⟨hpPrime⟩
  have hsingletonBase :
      Ideal.primesOver (𝔭(p)) (NumberField.RingOfIntegers (Qsqrtd (d : ℚ))) = {P} :=
    primesOver_eq_singleton_of_mem_ramifiedPrimes (d := d) hp hP
  have hPprime : P.IsPrime := hP.1
  haveI : P.IsPrime := hPprime
  letI : P.LiesOver (𝔭(p)) := hP.2
  have hsingletonComap :
      Ideal.primesOver
          (P.comap (algebraMap ℤ (NumberField.RingOfIntegers (Qsqrtd (d : ℚ)))))
          (NumberField.RingOfIntegers (Qsqrtd (d : ℚ))) = {P} := by
    change Ideal.primesOver (P.under ℤ)
      (NumberField.RingOfIntegers (Qsqrtd (d : ℚ))) = {P}
    rw [← Ideal.LiesOver.over (p := 𝔭(p)) (P := P)]
    exact hsingletonBase
  exact map_conjAut_eq_of_primesOver_comap_eq_singleton
    (K := Qsqrtd (d : ℚ)) P hsingletonComap

/-- If a prime ideal lies over a rational prime in the genus-theory ramified-prime
set, then conjugation fixes it. This comap form is the interface used after
choosing the rational prime below a prime ideal factor. -/
theorem map_conjAut_eq_of_comap_eq_of_mem_ramifiedPrimes
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)]
    {p : ℕ} (hp : p ∈ ramifiedPrimes d)
    {P : Ideal (NumberField.RingOfIntegers (Qsqrtd (d : ℚ)))} [P.IsPrime]
    (hcomap : P.comap (algebraMap ℤ (NumberField.RingOfIntegers (Qsqrtd (d : ℚ)))) =
      𝔭(p)) :
    Ideal.map (conjAutRingOfIntegers (Qsqrtd (d : ℚ)) :
      NumberField.RingOfIntegers (Qsqrtd (d : ℚ)) →+*
        NumberField.RingOfIntegers (Qsqrtd (d : ℚ))) P = P := by
  letI : P.LiesOver (𝔭(p)) := ⟨hcomap.symm⟩
  exact map_conjAut_eq_of_mem_primesOver_of_mem_ramifiedPrimes (d := d) hp
    (P := P) ⟨inferInstance, inferInstance⟩

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

theorem exists_nat_prime_comap_eq_p_and_dvd_absNorm
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)]
    {P : Ideal (NumberField.RingOfIntegers (Qsqrtd (d : ℚ)))}
    (hP : P.IsPrime) (hP0 : P ≠ ⊥) :
    ∃ p : ℕ, p.Prime ∧
      P.comap (algebraMap ℤ (NumberField.RingOfIntegers (Qsqrtd (d : ℚ)))) = 𝔭(p) ∧
        p ∣ Ideal.absNorm P := by
  exact Ideal.exists_nat_prime_comap_eq_span_and_dvd_absNorm_of_isPrime hP hP0

theorem map_span_eq_of_isInertIn_of_comap_eq_p
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)]
    {P : Ideal (NumberField.RingOfIntegers (Qsqrtd (d : ℚ)))}
    (hP : P.IsPrime) {p : ℕ} (hp : p.Prime)
    (hcomap :
      P.comap (algebraMap ℤ (NumberField.RingOfIntegers (Qsqrtd (d : ℚ)))) = 𝔭(p))
    (hinert : Ideal.IsInertIn (𝔭(p))
      (NumberField.RingOfIntegers (Qsqrtd (d : ℚ)))) :
    Ideal.map (algebraMap ℤ (NumberField.RingOfIntegers (Qsqrtd (d : ℚ)))) (𝔭(p)) =
      P := by
  have hchar : ringChar ℤ ≠ 2 := by simp [ringChar.eq_zero]
  have hpbot : (𝔭(p)) ≠ (⊥ : Ideal ℤ) := by
    rw [Ne, Ideal.span_singleton_eq_bot, Nat.cast_eq_zero]
    exact hp.ne_zero
  haveI : (𝔭(p)).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible
      ((Nat.prime_iff_prime_int.mp hp).irreducible)
  have hQprime :
      (Ideal.map (algebraMap ℤ (NumberField.RingOfIntegers (Qsqrtd (d : ℚ))))
        (𝔭(p))).IsPrime :=
    Ideal.map_isPrime_of_isInertIn (𝔭(p))
      (NumberField.RingOfIntegers (Qsqrtd (d : ℚ))) hchar hpbot hinert
  have hQle :
      Ideal.map (algebraMap ℤ (NumberField.RingOfIntegers (Qsqrtd (d : ℚ)))) (𝔭(p)) ≤
        P := by
    rw [← hcomap]
    exact Ideal.map_comap_le
  have hQbot :
      Ideal.map (algebraMap ℤ (NumberField.RingOfIntegers (Qsqrtd (d : ℚ)))) (𝔭(p)) ≠
        ⊥ := by
    rw [Ideal.map_span, Set.image_singleton, Ne, Ideal.span_singleton_eq_bot]
    simp only [map_natCast, Nat.cast_eq_zero]
    exact hp.ne_zero
  exact (hQprime.isMaximal hQbot).eq_of_le hP.ne_top hQle

theorem isPrincipal_of_isInertIn_of_comap_eq_p
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)]
    {P : Ideal (NumberField.RingOfIntegers (Qsqrtd (d : ℚ)))}
    (hP : P.IsPrime) {p : ℕ} (hp : p.Prime)
    (hcomap :
      P.comap (algebraMap ℤ (NumberField.RingOfIntegers (Qsqrtd (d : ℚ)))) = 𝔭(p))
    (hinert : Ideal.IsInertIn (𝔭(p))
      (NumberField.RingOfIntegers (Qsqrtd (d : ℚ)))) :
    P.IsPrincipal := by
  have hPQ := map_span_eq_of_isInertIn_of_comap_eq_p (d := d) hP hp hcomap hinert
  rw [← hPQ, Ideal.map_span, Set.image_singleton]
  exact ⟨_, rfl⟩

theorem map_span_eq_sq_of_isRamifiedIn_of_mem_primesOver
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] {p : ℕ} (hp : p.Prime)
    {P : Ideal (NumberField.RingOfIntegers (Qsqrtd (d : ℚ)))}
    (hP : P ∈ Ideal.primesOver (𝔭(p))
      (NumberField.RingOfIntegers (Qsqrtd (d : ℚ))))
    (hram : Ideal.IsRamifiedIn (𝔭(p))
      (NumberField.RingOfIntegers (Qsqrtd (d : ℚ)))) :
    Ideal.map (algebraMap ℤ (NumberField.RingOfIntegers (Qsqrtd (d : ℚ)))) (𝔭(p)) =
      P ^ 2 := by
  have hchar : ringChar ℤ ≠ 2 := by simp [ringChar.eq_zero]
  have hpbot : (𝔭(p)) ≠ (⊥ : Ideal ℤ) := by
    rw [Ne, Ideal.span_singleton_eq_bot, Nat.cast_eq_zero]
    exact hp.ne_zero
  haveI : (𝔭(p)).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible
      ((Nat.prime_iff_prime_int.mp hp).irreducible)
  obtain ⟨Q, hQ, hmap⟩ :=
    Ideal.map_eq_sq_of_isRamifiedIn (𝔭(p))
      (NumberField.RingOfIntegers (Qsqrtd (d : ℚ))) hchar hpbot hram
  have hsingleton :
      Ideal.primesOver (𝔭(p)) (NumberField.RingOfIntegers (Qsqrtd (d : ℚ))) = {P} :=
    primesOver_eq_singleton_of_isRamifiedIn
      (S := NumberField.RingOfIntegers (Qsqrtd (d : ℚ))) (p := 𝔭(p))
      hchar hpbot hP hram
  have hQP : Q = P := by
    have hQmem : Q ∈ ({P} : Set (Ideal (NumberField.RingOfIntegers (Qsqrtd (d : ℚ))))) := by
      simpa [hsingleton] using hQ
    simpa using hQmem
  simpa [hQP] using hmap

theorem primesOver_ncard_eq_two_of_isSplitIn
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [Nontrivial R] [IsDedekindDomain R] [IsDedekindDomain S]
    [Algebra.IsQuadraticExtension R S]
    {p : Ideal R} (hchar : ringChar R ≠ 2) (hp : p ≠ ⊥) [p.IsMaximal]
    (hsplit : Ideal.IsSplitIn p S) :
    (Ideal.primesOver p S).ncard = 2 :=
  ((Ideal.ramificationIdxIn_eq_one_and_inertiaDegIn_eq_one_iff_efg p S hchar hp).mp
    hsplit).1

/-- Over a split rational prime, quadratic conjugation swaps the two prime ideals
above it rather than fixing either one. -/
theorem map_conjAut_ne_of_mem_primesOver_of_isSplitIn
    (K : Type*) [Field K] [NumberField K] [Algebra ℚ K]
    [QuadraticField K] [QuadraticField.Conj K]
    {p : Ideal ℤ} (hp0 : p ≠ ⊥) [p.IsMaximal]
    {P : Ideal (NumberField.RingOfIntegers K)}
    (hP : P ∈ Ideal.primesOver p (NumberField.RingOfIntegers K))
    (hsplit : Ideal.IsSplitIn p (NumberField.RingOfIntegers K)) :
    Ideal.map (conjAutRingOfIntegers K :
      NumberField.RingOfIntegers K →+* NumberField.RingOfIntegers K) P ≠ P := by
  intro hfix
  haveI : P.IsPrime := hP.1
  haveI : IsGalois ℚ K := Algebra.IsQuadraticExtension.isGalois ℚ K
  haveI : IsGalois (FractionRing ℤ) (FractionRing (NumberField.RingOfIntegers K)) :=
    NumberField.isGalois_fractionRing_ringOfIntegers K
  let τ : Gal(FractionRing (NumberField.RingOfIntegers K) / FractionRing ℤ) :=
    (galRestrict ℤ (FractionRing ℤ) (FractionRing (NumberField.RingOfIntegers K))
      (NumberField.RingOfIntegers K)).symm
      (conjAutRingOfIntegersAlgEquiv K)
  letI := Ring.instAlgebraFractionRing
  letI := IsIntegralClosure.MulSemiringAction ℤ (FractionRing ℤ)
    (FractionRing (NumberField.RingOfIntegers K)) (NumberField.RingOfIntegers K)
  letI := Algebra.IsQuadraticExtension.isGaloisGroup
    (R := ℤ) (S := NumberField.RingOfIntegers K) (by norm_num : ringChar ℤ ≠ 2)
  have hτne : τ ≠ 1 := by
    intro hτ
    apply conjAutRingOfIntegersAlgEquiv_ne_refl (K := K)
    have h := congrArg
      (galRestrict ℤ (FractionRing ℤ) (FractionRing (NumberField.RingOfIntegers K))
        (NumberField.RingOfIntegers K)) hτ
    simpa [τ] using h
  have hτstab :
      τ ∈ MulAction.stabilizer
          Gal(FractionRing (NumberField.RingOfIntegers K) / FractionRing ℤ) P := by
    change τ • P = P
    change Ideal.map
      ((galRestrict ℤ (FractionRing ℤ) (FractionRing (NumberField.RingOfIntegers K))
        (NumberField.RingOfIntegers K) τ :
          NumberField.RingOfIntegers K ≃ₐ[ℤ] NumberField.RingOfIntegers K) :
            NumberField.RingOfIntegers K →+* NumberField.RingOfIntegers K) P = P
    dsimp [τ]
    rw [MulEquiv.apply_symm_apply]
    exact hfix
  have hcard_stab :
      Nat.card (MulAction.stabilizer
        Gal(FractionRing (NumberField.RingOfIntegers K) / FractionRing ℤ) P) = 1 := by
    haveI : P.LiesOver p := hP.2
    have horbit :
        MulAction.orbit
            Gal(FractionRing (NumberField.RingOfIntegers K) / FractionRing ℤ) P =
          Ideal.primesOver p (NumberField.RingOfIntegers K) := by
      exact Algebra.IsInvariant.orbit_eq_primesOver ℤ (NumberField.RingOfIntegers K)
        Gal(FractionRing (NumberField.RingOfIntegers K) / FractionRing ℤ) p P
    have horbit_card :
        Nat.card (MulAction.orbit
          Gal(FractionRing (NumberField.RingOfIntegers K) / FractionRing ℤ) P) = 2 := by
      rw [horbit]
      change (Ideal.primesOver p (NumberField.RingOfIntegers K)).ncard = 2
      exact primesOver_ncard_eq_two_of_isSplitIn
        (S := NumberField.RingOfIntegers K) (p := p) (by simp [ringChar.eq_zero])
        hp0 hsplit
    have hprod :
        Nat.card (MulAction.orbit
            Gal(FractionRing (NumberField.RingOfIntegers K) / FractionRing ℤ) P) *
            Nat.card (MulAction.stabilizer
              Gal(FractionRing (NumberField.RingOfIntegers K) / FractionRing ℤ) P) =
          Nat.card Gal(FractionRing (NumberField.RingOfIntegers K) / FractionRing ℤ) := by
      simpa [Nat.card_prod] using
        Nat.card_congr
          (MulAction.orbitProdStabilizerEquivGroup
            Gal(FractionRing (NumberField.RingOfIntegers K) / FractionRing ℤ) P)
    rw [horbit_card, card_gal_fractionRing_ringOfIntegers_eq_two K] at hprod
    omega
  have hsub :
      Subsingleton (MulAction.stabilizer
        Gal(FractionRing (NumberField.RingOfIntegers K) / FractionRing ℤ) P) :=
    (Nat.card_eq_one_iff_unique.mp hcard_stab).1
  have hτeq : τ = 1 := by
    have hsubeq :
        (⟨τ, hτstab⟩ :
          MulAction.stabilizer
            Gal(FractionRing (NumberField.RingOfIntegers K) / FractionRing ℤ) P) = 1 :=
      Subsingleton.elim _ _
    exact Subtype.ext_iff.mp hsubeq
  exact hτne hτeq

theorem set_eq_pair_of_ncard_eq_two_of_mem_of_mem_of_ne
    {α : Type*} {s : Set α} {a b : α}
    (hs : s.ncard = 2) (ha : a ∈ s) (hb : b ∈ s) (hne : a ≠ b) :
    s = {a, b} := by
  have hpair : ({a, b} : Set α).ncard = 2 := Set.ncard_pair hne
  have hsfinite : s.Finite := by
    rw [Set.ncard_eq_two] at hs
    obtain ⟨x, y, _hxy, rfl⟩ := hs
    simp
  refine (Set.eq_of_subset_of_ncard_le ?_ ?_ hsfinite).symm
  · intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · exact ha
    · exact hb
  · simp [hs, hpair]

theorem map_eq_mul_of_isSplitIn_of_mem_primesOver_of_ne
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [Nontrivial R] [IsDedekindDomain R] [IsDedekindDomain S]
    [Algebra.IsQuadraticExtension R S] [Algebra.IsIntegral R S]
    [Module.IsTorsionFree R S]
    {p : Ideal R} (hchar : ringChar R ≠ 2) (hp : p ≠ ⊥) [p.IsMaximal]
    {P Q : Ideal S} (hP : P ∈ Ideal.primesOver p S) (hQ : Q ∈ Ideal.primesOver p S)
    (hne : P ≠ Q) (hsplit : Ideal.IsSplitIn p S) :
    Ideal.map (algebraMap R S) p = P * Q := by
  have hfiber : Ideal.primesOver p S = {P, Q} :=
    set_eq_pair_of_ncard_eq_two_of_mem_of_mem_of_ne
      (primesOver_ncard_eq_two_of_isSplitIn hchar hp hsplit) hP hQ hne
  obtain ⟨P₁, hP₁, P₂, hP₂, hPne, hmap⟩ :=
    Ideal.map_eq_of_isSplitIn p S hchar hp hsplit
  have hP₁' : P₁ = P ∨ P₁ = Q := by
    have hmem : P₁ ∈ ({P, Q} : Set (Ideal S)) := by
      simpa [hfiber] using hP₁
    simpa using hmem
  have hP₂' : P₂ = P ∨ P₂ = Q := by
    have hmem : P₂ ∈ ({P, Q} : Set (Ideal S)) := by
      simpa [hfiber] using hP₂
    simpa using hmem
  rcases hP₁' with rfl | rfl <;> rcases hP₂' with rfl | rfl
  · exact False.elim (hPne rfl)
  · exact hmap
  · simpa [mul_comm] using hmap
  · exact False.elim (hPne rfl)

/-- A prime factor of an ambiguous ideal contributes a base-prime principal
factor in each splitting case. This span form preserves the positive rational
generator needed later for the narrow principal multiplier. -/
theorem factor_contribution_by_splitting_span
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)]
    {P : Ideal (NumberField.RingOfIntegers (Qsqrtd (d : ℚ)))}
    {I : (Ideal (NumberField.RingOfIntegers (Qsqrtd (d : ℚ))))⁰}
    (hI : IsAmbiguousIdeal (conjAutRingOfIntegers (Qsqrtd (d : ℚ))) I.1)
    (hP : P ∈ UniqueFactorizationMonoid.normalizedFactors I.1)
    {p : ℕ} (hp : p.Prime)
    (hcomap : P.comap
      (algebraMap ℤ (NumberField.RingOfIntegers (Qsqrtd (d : ℚ)))) = 𝔭(p)) :
    (Ideal.IsSplitIn (𝔭(p)) (NumberField.RingOfIntegers (Qsqrtd (d : ℚ))) ∧
        P * Ideal.map
          (conjAutRingOfIntegers (Qsqrtd (d : ℚ)) :
            NumberField.RingOfIntegers (Qsqrtd (d : ℚ)) →+*
              NumberField.RingOfIntegers (Qsqrtd (d : ℚ))) P =
          Ideal.span ({(p : NumberField.RingOfIntegers (Qsqrtd (d : ℚ)))} : Set
            (NumberField.RingOfIntegers (Qsqrtd (d : ℚ))))) ∨
      (Ideal.IsInertIn (𝔭(p)) (NumberField.RingOfIntegers (Qsqrtd (d : ℚ))) ∧
        P = Ideal.span ({(p : NumberField.RingOfIntegers (Qsqrtd (d : ℚ)))} : Set
          (NumberField.RingOfIntegers (Qsqrtd (d : ℚ))))) ∨
        (Ideal.IsRamifiedIn (𝔭(p)) (NumberField.RingOfIntegers (Qsqrtd (d : ℚ))) ∧
          P ^ 2 = Ideal.span ({(p : NumberField.RingOfIntegers (Qsqrtd (d : ℚ)))} :
            Set (NumberField.RingOfIntegers (Qsqrtd (d : ℚ))))) := by
  let R := NumberField.RingOfIntegers (Qsqrtd (d : ℚ))
  have hI0 : I.1 ≠ ⊥ := by
    rw [← Ideal.zero_eq_bot]
    exact mem_nonZeroDivisors_iff_ne_zero.mp I.2
  have hPprime : P.IsPrime := (Ideal.mem_normalizedFactors_iff hI0).mp hP |>.1
  have hPover : P ∈ Ideal.primesOver (𝔭(p)) R := ⟨hPprime, ⟨hcomap.symm⟩⟩
  have hpbot : (𝔭(p)) ≠ (⊥ : Ideal ℤ) := by
    rw [Ne, Ideal.span_singleton_eq_bot, Nat.cast_eq_zero]
    exact hp.ne_zero
  haveI : (𝔭(p)).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible
      ((Nat.prime_iff_prime_int.mp hp).irreducible)
  have hmapSpan :
      Ideal.map (algebraMap ℤ R) (𝔭(p)) =
        Ideal.span ({(p : R)} : Set R) := by
    rw [Ideal.map_span, Set.image_singleton]
    rfl
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
      map_eq_mul_of_isSplitIn_of_mem_primesOver_of_ne
        (S := R) (p := 𝔭(p)) (by simp [ringChar.eq_zero]) hpbot
        hPover hconjOver hne hsplit
    exact Or.inl ⟨hsplit, hmap.symm.trans hmapSpan⟩
  · have hmap :=
      map_span_eq_of_isInertIn_of_comap_eq_p (d := d) hPprime hp hcomap hinert
    exact Or.inr <| Or.inl ⟨hinert, hmap.symm.trans hmapSpan⟩
  · have hmap :
        Ideal.map (algebraMap ℤ R) (𝔭(p)) = P ^ 2 :=
      map_span_eq_sq_of_isRamifiedIn_of_mem_primesOver (d := d) hp hPover hram
    exact Or.inr <| Or.inr ⟨hram, hmap.symm.trans hmapSpan⟩

/-- A prime factor of an ambiguous ideal contributes either a principal split
pair, a principal inert factor, or a ramified square. -/
theorem factor_contribution_by_splitting
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)]
    {P : Ideal (NumberField.RingOfIntegers (Qsqrtd (d : ℚ)))}
    {I : (Ideal (NumberField.RingOfIntegers (Qsqrtd (d : ℚ))))⁰}
    (hI : IsAmbiguousIdeal (conjAutRingOfIntegers (Qsqrtd (d : ℚ))) I.1)
    (hP : P ∈ UniqueFactorizationMonoid.normalizedFactors I.1)
    {p : ℕ} (hp : p.Prime)
    (hcomap : P.comap
      (algebraMap ℤ (NumberField.RingOfIntegers (Qsqrtd (d : ℚ)))) = 𝔭(p)) :
    (Ideal.IsSplitIn (𝔭(p)) (NumberField.RingOfIntegers (Qsqrtd (d : ℚ))) ∧
        (P * Ideal.map
          (conjAutRingOfIntegers (Qsqrtd (d : ℚ)) :
            NumberField.RingOfIntegers (Qsqrtd (d : ℚ)) →+*
              NumberField.RingOfIntegers (Qsqrtd (d : ℚ))) P).IsPrincipal) ∨
      (Ideal.IsInertIn (𝔭(p)) (NumberField.RingOfIntegers (Qsqrtd (d : ℚ))) ∧
        P.IsPrincipal) ∨
        (Ideal.IsRamifiedIn (𝔭(p)) (NumberField.RingOfIntegers (Qsqrtd (d : ℚ))) ∧
          (P ^ 2).IsPrincipal) := by
  rcases factor_contribution_by_splitting_span d hI hP hp hcomap with hsplit | hinert | hram
  · exact Or.inl ⟨hsplit.1, ⟨_, hsplit.2⟩⟩
  · exact Or.inr <| Or.inl ⟨hinert.1, ⟨_, hinert.2⟩⟩
  · exact Or.inr <| Or.inr ⟨hram.1, ⟨_, hram.2⟩⟩

/-- Prime-ideal form of the Galois-orbit calculation: extending the norm prime
power back to the ring of integers gives the product of `P` with its conjugate. -/
theorem map_comap_pow_inertiaDeg_eq_mul_map_conjAut_of_isPrime
    (K : Type*) [Field K] [NumberField K] [Algebra ℚ K]
    [QuadraticField K] [QuadraticField.Conj K]
    (P : Ideal (NumberField.RingOfIntegers K)) [P.IsPrime] (hP0 : P ≠ ⊥) :
    Ideal.map (algebraMap ℤ (NumberField.RingOfIntegers K))
        ((P.comap (algebraMap ℤ (NumberField.RingOfIntegers K))) ^
          (P.comap (algebraMap ℤ (NumberField.RingOfIntegers K))).inertiaDeg P) =
      P * Ideal.map (conjAutRingOfIntegers K :
        NumberField.RingOfIntegers K →+* NumberField.RingOfIntegers K) P := by
  let p : Ideal ℤ := P.comap (algebraMap ℤ (NumberField.RingOfIntegers K))
  haveI : P.IsMaximal := Ideal.IsPrime.isMaximal inferInstance hP0
  haveI : p.IsMaximal := by
    dsimp [p]
    exact Ideal.isMaximal_comap_of_isIntegral_of_isMaximal P
  have hp0 : p ≠ ⊥ := by
    dsimp [p]
    exact Ideal.IsIntegralClosure.comap_ne_bot K hP0
  have hPmem : P ∈ Ideal.primesOver p (NumberField.RingOfIntegers K) := by
    dsimp [p]
    exact ⟨inferInstance, ⟨rfl⟩⟩
  have hσmem :
      Ideal.map (conjAutRingOfIntegers K :
          NumberField.RingOfIntegers K →+* NumberField.RingOfIntegers K) P ∈
        Ideal.primesOver p (NumberField.RingOfIntegers K) := by
    dsimp [p]
    exact map_conjAut_mem_primesOver_comap K P
  have htri :=
    Ideal.efg_trichotomy p (NumberField.RingOfIntegers K)
      (by norm_num : ringChar ℤ ≠ 2) hp0
  rcases htri with hsplit | hinert | hram
  · let σP : Ideal (NumberField.RingOfIntegers K) :=
      Ideal.map (conjAutRingOfIntegers K :
        NumberField.RingOfIntegers K →+* NumberField.RingOfIntegers K) P
    have hsplit' : Ideal.IsSplitIn p (NumberField.RingOfIntegers K) :=
      ⟨hsplit.2.1, hsplit.2.2⟩
    have hσne : σP ≠ P := by
      dsimp [σP]
      exact map_conjAut_ne_of_mem_primesOver_of_isSplitIn K hp0 hPmem hsplit'
    have hfP : p.inertiaDeg P = 1 :=
      Ideal.inertiaDeg_eq_one_of_isSplitIn p (NumberField.RingOfIntegers K)
        (by norm_num : ringChar ℤ ≠ 2) (P' := P) hsplit'
    have hmap :
        Ideal.map (algebraMap ℤ (NumberField.RingOfIntegers K)) p = P * σP := by
      exact map_eq_mul_of_isSplitIn_of_mem_primesOver_of_ne
        (S := NumberField.RingOfIntegers K) (p := p)
        (by norm_num : ringChar ℤ ≠ 2) hp0 hPmem hσmem hσne.symm hsplit'
    change Ideal.map (algebraMap ℤ (NumberField.RingOfIntegers K)) (p ^ p.inertiaDeg P) =
      P * Ideal.map (conjAutRingOfIntegers K :
        NumberField.RingOfIntegers K →+* NumberField.RingOfIntegers K) P
    rw [hfP, pow_one, hmap]
  · have hsingleton :
        Ideal.primesOver p (NumberField.RingOfIntegers K) = {P} := by
      rw [Set.ncard_eq_one] at hinert
      obtain ⟨Q, hQ⟩ := hinert.1
      have hPQ : P = Q := by
        rw [hQ] at hPmem
        exact hPmem
      rw [← hPQ] at hQ
      exact hQ
    have hσP :
        Ideal.map (conjAutRingOfIntegers K :
          NumberField.RingOfIntegers K →+* NumberField.RingOfIntegers K) P = P := by
      rw [hsingleton] at hσmem
      exact hσmem
    have hfP : p.inertiaDeg P = 2 := by
      rw [← Ideal.inertiaDegIn_eq_inertiaDeg_of_primesOver_eq_singleton
        (p := p) (S := NumberField.RingOfIntegers K) (P := P) hsingleton]
      exact hinert.2.2
    have hmap :
        Ideal.map (algebraMap ℤ (NumberField.RingOfIntegers K)) p = P := by
      have hfact :=
        Ideal.map_algebraMap_eq_finset_prod_pow
          (R := NumberField.RingOfIntegers K) (S := ℤ) hp0
      have heP : p.ramificationIdx P = 1 := by
        rw [← Ideal.ramificationIdxIn_eq_ramificationIdx_of_primesOver_eq_singleton
          (p := p) (S := NumberField.RingOfIntegers K) (P := P) hsingleton]
        exact hinert.2.1
      have hfin : (Ideal.primesOver p (NumberField.RingOfIntegers K)).toFinset = {P} := by
        ext Q
        simp [hsingleton]
      rw [hfin] at hfact
      simpa [heP] using hfact
    change Ideal.map (algebraMap ℤ (NumberField.RingOfIntegers K)) (p ^ p.inertiaDeg P) =
      P * Ideal.map (conjAutRingOfIntegers K :
        NumberField.RingOfIntegers K →+* NumberField.RingOfIntegers K) P
    rw [hfP, Ideal.map_pow, hmap, hσP, pow_two]
  · have hsingleton :
        Ideal.primesOver p (NumberField.RingOfIntegers K) = {P} := by
      rw [Set.ncard_eq_one] at hram
      obtain ⟨Q, hQ⟩ := hram.1
      have hPQ : P = Q := by
        rw [hQ] at hPmem
        exact hPmem
      rw [← hPQ] at hQ
      exact hQ
    have hσP :
        Ideal.map (conjAutRingOfIntegers K :
          NumberField.RingOfIntegers K →+* NumberField.RingOfIntegers K) P = P := by
      rw [hsingleton] at hσmem
      exact hσmem
    have hfP : p.inertiaDeg P = 1 := by
      rw [← Ideal.inertiaDegIn_eq_inertiaDeg_of_primesOver_eq_singleton
        (p := p) (S := NumberField.RingOfIntegers K) (P := P) hsingleton]
      exact hram.2.2
    have hmap :
        Ideal.map (algebraMap ℤ (NumberField.RingOfIntegers K)) p = P ^ 2 := by
      have hfact :=
        Ideal.map_algebraMap_eq_finset_prod_pow
          (R := NumberField.RingOfIntegers K) (S := ℤ) hp0
      have heP : p.ramificationIdx P = 2 := by
        rw [← Ideal.ramificationIdxIn_eq_ramificationIdx_of_primesOver_eq_singleton
          (p := p) (S := NumberField.RingOfIntegers K) (P := P) hsingleton]
        exact hram.2.1
      have hfin : (Ideal.primesOver p (NumberField.RingOfIntegers K)).toFinset = {P} := by
        ext Q
        simp [hsingleton]
      rw [hfin] at hfact
      simpa [heP] using hfact
    change Ideal.map (algebraMap ℤ (NumberField.RingOfIntegers K)) (p ^ p.inertiaDeg P) =
      P * Ideal.map (conjAutRingOfIntegers K :
        NumberField.RingOfIntegers K →+* NumberField.RingOfIntegers K) P
    rw [hfP, pow_one, hmap, hσP, pow_two]

/-- Prime-ideal case of the conjugation/norm identity. -/
theorem mul_map_conjAut_eq_map_relNorm_of_isPrime
    (K : Type*) [Field K] [NumberField K] [Algebra ℚ K]
    [QuadraticField K] [QuadraticField.Conj K]
    (P : Ideal (NumberField.RingOfIntegers K)) [P.IsPrime] :
    P * Ideal.map (conjAutRingOfIntegers K :
        NumberField.RingOfIntegers K →+* NumberField.RingOfIntegers K) P =
      Ideal.map (algebraMap ℤ (NumberField.RingOfIntegers K)) (Ideal.relNorm ℤ P) := by
  by_cases hP0 : P = ⊥
  · simp [hP0, Ideal.relNorm_bot]
  · rw [relNorm_eq_comap_pow_inertiaDeg_of_isPrime K P hP0,
      map_comap_pow_inertiaDeg_eq_mul_map_conjAut_of_isPrime K P hP0]

/-- Multiplicative assembly of the conjugation/norm identity from the prime
ideal case. -/
theorem mul_map_conjAut_eq_map_relNorm_of_prime_cases
    (K : Type*) [Field K] [NumberField K] [Algebra ℚ K]
    [QuadraticField K] [QuadraticField.Conj K]
    (hprime : ∀ P : Ideal (NumberField.RingOfIntegers K), P.IsPrime →
      P * Ideal.map (conjAutRingOfIntegers K :
          NumberField.RingOfIntegers K →+* NumberField.RingOfIntegers K) P =
        Ideal.map (algebraMap ℤ (NumberField.RingOfIntegers K)) (Ideal.relNorm ℤ P))
    (I : Ideal (NumberField.RingOfIntegers K)) :
    I * Ideal.map (conjAutRingOfIntegers K :
        NumberField.RingOfIntegers K →+* NumberField.RingOfIntegers K) I =
      Ideal.map (algebraMap ℤ (NumberField.RingOfIntegers K)) (Ideal.relNorm ℤ I) := by
  by_cases hI : I = ⊥
  · simp [hI, Ideal.relNorm_bot]
  rw [← Ideal.prod_normalizedFactors_eq_self hI]
  refine Multiset.prod_induction
      (fun J : Ideal (NumberField.RingOfIntegers K) =>
        J * Ideal.map (conjAutRingOfIntegers K :
            NumberField.RingOfIntegers K →+* NumberField.RingOfIntegers K) J =
          Ideal.map (algebraMap ℤ (NumberField.RingOfIntegers K)) (Ideal.relNorm ℤ J))
      _ ?_ ?_ ?_
  · intro J L hJ hL
    rw [Ideal.map_mul, map_mul, Ideal.map_mul]
    calc
      J * L * (Ideal.map (conjAutRingOfIntegers K :
            NumberField.RingOfIntegers K →+* NumberField.RingOfIntegers K) J *
          Ideal.map (conjAutRingOfIntegers K :
            NumberField.RingOfIntegers K →+* NumberField.RingOfIntegers K) L) =
          (J * Ideal.map (conjAutRingOfIntegers K :
              NumberField.RingOfIntegers K →+* NumberField.RingOfIntegers K) J) *
            (L * Ideal.map (conjAutRingOfIntegers K :
              NumberField.RingOfIntegers K →+* NumberField.RingOfIntegers K) L) := by
        ac_rfl
      _ = Ideal.map (algebraMap ℤ (NumberField.RingOfIntegers K)) (Ideal.relNorm ℤ J) *
          Ideal.map (algebraMap ℤ (NumberField.RingOfIntegers K)) (Ideal.relNorm ℤ L) := by
        rw [hJ, hL]
  · simp [Ideal.relNorm_top, Ideal.map_top]
  · intro Q hQ
    rw [Ideal.mem_normalizedFactors_iff hI] at hQ
    exact hprime Q hQ.1

/-- Product of an ideal with its quadratic conjugate is the extension of its
relative norm. -/
theorem mul_map_conjAut_eq_map_relNorm
    (K : Type*) [Field K] [NumberField K] [Algebra ℚ K]
    [QuadraticField K] [QuadraticField.Conj K]
    (I : Ideal (NumberField.RingOfIntegers K)) :
    I * Ideal.map (conjAutRingOfIntegers K :
        NumberField.RingOfIntegers K →+* NumberField.RingOfIntegers K) I =
      Ideal.map (algebraMap ℤ (NumberField.RingOfIntegers K)) (Ideal.relNorm ℤ I) := by
  refine mul_map_conjAut_eq_map_relNorm_of_prime_cases K ?_ I
  intro P hP
  haveI : P.IsPrime := hP
  exact mul_map_conjAut_eq_map_relNorm_of_isPrime K P

/-- The product of a nonzero ideal with its quadratic conjugate is principal. -/
theorem exists_span_mul_map_conjAut
    (K : Type*) [Field K] [NumberField K] [Algebra ℚ K]
    [QuadraticField K] [QuadraticField.Conj K]
    {I : Ideal (NumberField.RingOfIntegers K)} (hI : I ≠ ⊥) :
    ∃ x : NumberField.RingOfIntegers K, x ≠ 0 ∧
      I * Ideal.map (conjAutRingOfIntegers K :
          NumberField.RingOfIntegers K →+* NumberField.RingOfIntegers K) I =
        Ideal.span {x} := by
  have hrel : Ideal.relNorm ℤ I ≠ ⊥ := by
    rw [ne_eq, ← Ideal.spanNorm_eq, Ideal.spanNorm_eq_bot_iff]
    exact hI
  obtain ⟨n, hn⟩ := IsPrincipalIdealRing.principal (Ideal.relNorm ℤ I)
  rw [Ideal.submodule_span_eq] at hn
  have hn0 : n ≠ 0 := by
    rintro rfl
    exact hrel (by rw [hn, Ideal.span_singleton_eq_bot.mpr rfl])
  refine ⟨algebraMap ℤ (NumberField.RingOfIntegers K) n, ?_, ?_⟩
  · simpa only [map_zero] using
      (FaithfulSMul.algebraMap_injective ℤ (NumberField.RingOfIntegers K)).ne hn0
  · rw [mul_map_conjAut_eq_map_relNorm K, hn, Ideal.map_span, Set.image_singleton]

/-- The product of a nonzero ideal with its quadratic conjugate is generated by
its positive absolute norm. This is the narrow-class-group strengthening of
`exists_span_mul_map_conjAut`. -/
theorem mul_map_conjAut_eq_span_absNorm
    (K : Type*) [Field K] [NumberField K] [Algebra ℚ K]
    [QuadraticField K] [QuadraticField.Conj K]
    (I : Ideal (NumberField.RingOfIntegers K)) :
    I * Ideal.map (conjAutRingOfIntegers K :
        NumberField.RingOfIntegers K →+* NumberField.RingOfIntegers K) I =
      Ideal.span ({(Ideal.absNorm I :
        NumberField.RingOfIntegers K)} : Set (NumberField.RingOfIntegers K)) := by
  rw [mul_map_conjAut_eq_map_relNorm K]
  rw [Ideal.relNorm_int]
  rw [Ideal.map_span, Set.image_singleton]
  norm_num

/-- Quadratic conjugation acts on the ordinary ideal class group by inversion. -/
theorem mk0_map_conjAut_eq_inv
    (K : Type*) [Field K] [NumberField K] [Algebra ℚ K]
    [QuadraticField K] [QuadraticField.Conj K]
    (I : (Ideal (NumberField.RingOfIntegers K))⁰) :
    ClassGroup.mk0
        ⟨Ideal.map (conjAutRingOfIntegers K :
            NumberField.RingOfIntegers K →+* NumberField.RingOfIntegers K)
            (I : Ideal (NumberField.RingOfIntegers K)),
          map_conjAut_mem_nonZeroDivisors K I.2⟩ =
      (ClassGroup.mk0 I)⁻¹ := by
  have hI : (I : Ideal (NumberField.RingOfIntegers K)) ≠ ⊥ := by
    simpa [Ideal.zero_eq_bot] using mem_nonZeroDivisors_iff_ne_zero.mp I.2
  rw [ClassGroup.mk0_eq_mk0_inv_iff]
  obtain ⟨x, hx0, hx⟩ := exists_span_mul_map_conjAut K hI
  exact ⟨x, hx0, by rw [mul_comm]; exact hx⟩

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

/-- An ambiguous nonzero ideal represents a two-torsion class in the ordinary
ideal class group. -/
theorem mk0_sq_eq_one_of_isAmbiguousIdeal
    (K : Type*) [Field K] [NumberField K] [Algebra ℚ K]
    [QuadraticField K] [QuadraticField.Conj K]
    (I : (Ideal (NumberField.RingOfIntegers K))⁰)
    (hI : IsAmbiguousIdeal (conjAutRingOfIntegers K) I.1) :
    (ClassGroup.mk0 I : ClassGroup (NumberField.RingOfIntegers K)) ^ 2 = 1 := by
  have hfixed := (isAmbiguousIdeal_iff_conjAutNonzeroIdealMulEquiv_eq K I).mp hI
  have hconjClass :
      ClassGroup.mk0 (conjAutNonzeroIdealMulEquiv K I) = (ClassGroup.mk0 I)⁻¹ := by
    change ClassGroup.mk0
        ⟨Ideal.map (conjAutRingOfIntegers K :
            NumberField.RingOfIntegers K →+* NumberField.RingOfIntegers K)
          (I : Ideal (NumberField.RingOfIntegers K)),
          map_conjAut_mem_nonZeroDivisors K I.2⟩ =
      (ClassGroup.mk0 I)⁻¹
    exact mk0_map_conjAut_eq_inv K I
  rw [hfixed] at hconjClass
  have hmul :
      (ClassGroup.mk0 I : ClassGroup (NumberField.RingOfIntegers K)) * ClassGroup.mk0 I =
        1 :=
    eq_inv_iff_mul_eq_one.mp hconjClass
  simpa [pow_two] using hmul

theorem classGroup_mk0_eq_one_of_isPrincipal
    {R : Type*} [CommRing R] [IsDomain R] [IsDedekindDomain R]
    {J : Ideal R} (hJ0 : J ≠ ⊥) (hJ : J.IsPrincipal) :
    ClassGroup.mk0 ⟨J, mem_nonZeroDivisors_iff_ne_zero.mpr (by
      simpa [Ideal.zero_eq_bot] using hJ0)⟩ = (1 : ClassGroup R) :=
  (ClassGroup.mk0_eq_one_iff
    (mem_nonZeroDivisors_iff_ne_zero.mpr (by
      simpa [Ideal.zero_eq_bot] using hJ0))).mpr hJ

theorem classGroup_mk0_mul_eq_one_of_mul_isPrincipal
    {R : Type*} [CommRing R] [IsDomain R] [IsDedekindDomain R]
    {P Q : Ideal R} (hP0 : P ≠ ⊥) (hQ0 : Q ≠ ⊥) (hPQ : (P * Q).IsPrincipal) :
    ClassGroup.mk0 ⟨P, mem_nonZeroDivisors_iff_ne_zero.mpr (by
      simpa [Ideal.zero_eq_bot] using hP0)⟩ *
        ClassGroup.mk0 ⟨Q, mem_nonZeroDivisors_iff_ne_zero.mpr (by
          simpa [Ideal.zero_eq_bot] using hQ0)⟩ = (1 : ClassGroup R) := by
  let P0 : (Ideal R)⁰ :=
    ⟨P, mem_nonZeroDivisors_iff_ne_zero.mpr (by
      simpa [Ideal.zero_eq_bot] using hP0)⟩
  let Q0 : (Ideal R)⁰ :=
    ⟨Q, mem_nonZeroDivisors_iff_ne_zero.mpr (by
      simpa [Ideal.zero_eq_bot] using hQ0)⟩
  have hPQ0 : P * Q ∈ nonZeroDivisors (Ideal R) :=
    mul_mem_nonZeroDivisors_of_mem_nonZeroDivisors P0.2 Q0.2
  calc
    ClassGroup.mk0 P0 * ClassGroup.mk0 Q0 = ClassGroup.mk0 (P0 * Q0) := by
      rw [map_mul]
    _ = ClassGroup.mk0 ⟨P * Q, hPQ0⟩ := rfl
    _ = (1 : ClassGroup R) := (ClassGroup.mk0_eq_one_iff hPQ0).mpr hPQ

theorem classGroup_mk0_sq_eq_one_of_sq_isPrincipal
    {R : Type*} [CommRing R] [IsDomain R] [IsDedekindDomain R]
    {P : Ideal R} (hP0 : P ≠ ⊥) (hP2 : (P ^ 2).IsPrincipal) :
    (ClassGroup.mk0 ⟨P, mem_nonZeroDivisors_iff_ne_zero.mpr (by
      simpa [Ideal.zero_eq_bot] using hP0)⟩ : ClassGroup R) ^ 2 = 1 := by
  let P0 : (Ideal R)⁰ :=
    ⟨P, mem_nonZeroDivisors_iff_ne_zero.mpr (by
      simpa [Ideal.zero_eq_bot] using hP0)⟩
  calc
    (ClassGroup.mk0 P0 : ClassGroup R) ^ 2 = ClassGroup.mk0 (P0 ^ 2) := by
      rw [map_pow]
    _ = (1 : ClassGroup R) := (ClassGroup.mk0_eq_one_iff (P0 ^ 2).2).mpr hP2

end GenusTheory
end ClassGroup
end QuadraticNumberFields
