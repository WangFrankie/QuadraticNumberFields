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
import QuadraticNumberFields.ClassGroup.Genus.SquareClass
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
namespace Genus

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
private noncomputable def conjAutFractionRingAlgEquiv
    (K : Type*) [Field K] [NumberField K] [Algebra ℚ K]
    [QuadraticField K] [QuadraticField.Conj K] :
    FractionRing (NumberField.RingOfIntegers K) ≃ₐ[ℤ]
      FractionRing (NumberField.RingOfIntegers K) :=
  IsFractionRing.algEquivOfAlgEquiv (conjAutRingOfIntegersAlgEquiv K)

@[simp]
private theorem conjAutFractionRingAlgEquiv_algebraMap
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
private theorem fractionRing_algEquiv_conjAutFractionRingAlgEquiv
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
private theorem exists_mul_conjAutRingOfIntegers_eq_self_of_norm_eq_one
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

/-- Mapping ideals by a ring equivalence is injective. -/
private theorem ideal_map_ringEquiv_injective {R : Type*} [CommRing R] (σ : R ≃+* R) :
    Function.Injective (fun P : Ideal R => Ideal.map (σ : R →+* R) P) := by
  intro P Q hPQ
  change Ideal.map (σ : R →+* R) P = Ideal.map (σ : R →+* R) Q at hPQ
  have hP : Ideal.comap (σ : R →+* R) (Ideal.map (σ : R →+* R) P) = P :=
    Ideal.comap_map_of_bijective (f := (σ : R →+* R)) ⟨σ.injective, σ.surjective⟩
  have hQ : Ideal.comap (σ : R →+* R) (Ideal.map (σ : R →+* R) Q) = Q :=
    Ideal.comap_map_of_bijective (f := (σ : R →+* R)) ⟨σ.injective, σ.surjective⟩
  rw [← hP, hPQ, hQ]

/-- Mapping a multiset product of ideals by a ring equivalence maps each factor. -/
private theorem ideal_map_ringEquiv_multiset_prod {R : Type*} [CommRing R]
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
private theorem normalizedFactors_map_ringEquiv {R : Type*}
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
private theorem normalizedFactors_count_map_ringEquiv {R : Type*}
    [CommRing R] [IsDedekindDomain R] (σ : R ≃+* R)
    {P I : Ideal R} (hI : I ≠ ⊥) :
    (UniqueFactorizationMonoid.normalizedFactors (Ideal.map (σ : R →+* R) I)).count
        (Ideal.map (σ : R →+* R) P) =
      (UniqueFactorizationMonoid.normalizedFactors I).count P := by
  rw [normalizedFactors_map_ringEquiv σ hI]
  rw [Multiset.count_map_eq_count' _ _ (ideal_map_ringEquiv_injective σ) P]

/-- A ring equivalence preserves membership in the Dedekind ideal factorization
multiset. -/
private theorem map_ringEquiv_mem_normalizedFactors_iff {R : Type*}
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
private theorem exists_primesOver_eq_singleton_of_isRamifiedIn
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
private theorem primesOver_eq_singleton_of_isRamifiedIn
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

private noncomputable def ramifiedPrimeIdeal
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)]
    {p : ℕ} (hp : p ∈ ramifiedPrimes d) :
    Ideal (NumberField.RingOfIntegers (Qsqrtd (d : ℚ))) :=
  (exists_primesOver_eq_singleton_of_mem_ramifiedPrimes (d := d) hp).choose

private theorem primesOver_eq_singleton_ramifiedPrimeIdeal
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)]
    {p : ℕ} (hp : p ∈ ramifiedPrimes d) :
    Ideal.primesOver (𝔭(p)) (NumberField.RingOfIntegers (Qsqrtd (d : ℚ))) =
      {ramifiedPrimeIdeal d hp} :=
  (exists_primesOver_eq_singleton_of_mem_ramifiedPrimes (d := d) hp).choose_spec

private theorem ramifiedPrimeIdeal_mem_primesOver
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)]
    {p : ℕ} (hp : p ∈ ramifiedPrimes d) :
    ramifiedPrimeIdeal d hp ∈
      Ideal.primesOver (𝔭(p)) (NumberField.RingOfIntegers (Qsqrtd (d : ℚ))) := by
  rw [primesOver_eq_singleton_ramifiedPrimeIdeal]
  exact Set.mem_singleton _

private theorem ramifiedPrimeIdeal_ne_bot
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
private theorem ramifiedPrimeIdeal_eq_iff
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

private theorem exists_nat_prime_comap_eq_p_and_dvd_absNorm
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)]
    {P : Ideal (NumberField.RingOfIntegers (Qsqrtd (d : ℚ)))}
    (hP : P.IsPrime) (hP0 : P ≠ ⊥) :
    ∃ p : ℕ, p.Prime ∧
      P.comap (algebraMap ℤ (NumberField.RingOfIntegers (Qsqrtd (d : ℚ)))) = 𝔭(p) ∧
        p ∣ Ideal.absNorm P := by
  exact Ideal.exists_nat_prime_comap_eq_span_and_dvd_absNorm_of_isPrime hP hP0

private theorem map_span_eq_of_isInertIn_of_comap_eq_p
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

private theorem isPrincipal_of_isInertIn_of_comap_eq_p
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

private theorem map_span_eq_sq_of_isRamifiedIn_of_mem_primesOver
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

private theorem primesOver_ncard_eq_two_of_isSplitIn
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

private theorem set_eq_pair_of_ncard_eq_two_of_mem_of_mem_of_ne
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

private theorem map_eq_mul_of_isSplitIn_of_mem_primesOver_of_ne
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
private theorem factor_contribution_by_splitting_span
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
  · exact Or.inl ⟨hsplit.1, by rw [hsplit.2]; exact ⟨_, rfl⟩⟩
  · exact Or.inr <| Or.inl ⟨hinert.1, by rw [hinert.2]; exact ⟨_, rfl⟩⟩
  · exact Or.inr <| Or.inr ⟨hram.1, by rw [hram.2]; exact ⟨_, rfl⟩⟩

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
private theorem mul_map_conjAut_eq_span_absNorm
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

private theorem classGroup_mk0_eq_one_of_isPrincipal
    {R : Type*} [CommRing R] [IsDomain R] [IsDedekindDomain R]
    {J : Ideal R} (hJ0 : J ≠ ⊥) (hJ : J.IsPrincipal) :
    ClassGroup.mk0 ⟨J, mem_nonZeroDivisors_iff_ne_zero.mpr (by
      simpa [Ideal.zero_eq_bot] using hJ0)⟩ = (1 : ClassGroup R) :=
  (ClassGroup.mk0_eq_one_iff
    (mem_nonZeroDivisors_iff_ne_zero.mpr (by
      simpa [Ideal.zero_eq_bot] using hJ0))).mpr hJ

private theorem classGroup_mk0_mul_eq_one_of_mul_isPrincipal
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

private theorem classGroup_mk0_sq_eq_one_of_sq_isPrincipal
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

private noncomputable def idealRamifiedParityVector
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)]
    {p0 : ℕ} (_hp0 : p0 ∈ ramifiedPrimes d)
    (I : (Ideal (NumberField.RingOfIntegers (Qsqrtd (d : ℚ))))⁰) :
    ({p // p ∈ (ramifiedPrimes d).erase p0} → Fin 2) := by
  classical
  exact fun p =>
    ⟨(UniqueFactorizationMonoid.normalizedFactors I.1).count
        (ramifiedPrimeIdeal d ((Finset.mem_erase.mp p.2).2)) % 2,
      Nat.mod_lt _ (by decide : 0 < 2)⟩

private noncomputable def ramifiedPrimeNarrowClass
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)]
    {p : ℕ} (hp : p ∈ ramifiedPrimes d) :
    NarrowClassGroup (NumberField.RingOfIntegers (Qsqrtd (d : ℚ))) :=
  NarrowClassGroup.mk0
    ⟨ramifiedPrimeIdeal d hp,
      mem_nonZeroDivisors_iff_ne_zero.mpr (by
        simpa [Ideal.zero_eq_bot] using ramifiedPrimeIdeal_ne_bot d hp)⟩

private noncomputable def ramifiedParityIdealProduct
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

private noncomputable def fullRamifiedParityVector
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)]
    (I : (Ideal (NumberField.RingOfIntegers (Qsqrtd (d : ℚ))))⁰) :
    ({p // p ∈ ramifiedPrimes d} → Fin 2) := by
  classical
  exact fun p =>
    ⟨(UniqueFactorizationMonoid.normalizedFactors I.1).count
        (ramifiedPrimeIdeal d p.2) % 2,
      Nat.mod_lt _ (by decide : 0 < 2)⟩

private noncomputable def fullRamifiedParityIdealProduct
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)]
    (v : ({p // p ∈ ramifiedPrimes d} → Fin 2)) :
    (Ideal (NumberField.RingOfIntegers (Qsqrtd (d : ℚ))))⁰ := by
  classical
  exact Finset.univ.prod fun p : {p // p ∈ ramifiedPrimes d} =>
    if v p = 0 then 1 else
      ⟨ramifiedPrimeIdeal d p.2,
        mem_nonZeroDivisors_iff_ne_zero.mpr (by
          simpa [Ideal.zero_eq_bot] using ramifiedPrimeIdeal_ne_bot d p.2)⟩

/-- A ramified prime ideal is fixed by quadratic conjugation. -/
private theorem isAmbiguousIdeal_ramifiedPrimeIdeal
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)]
    {p : ℕ} (hp : p ∈ ramifiedPrimes d) :
    IsAmbiguousIdeal
      (conjAutRingOfIntegers (Qsqrtd (d : ℚ)))
      (ramifiedPrimeIdeal d hp) :=
  map_conjAut_eq_of_mem_primesOver_of_mem_ramifiedPrimes (d := d) hp
    (ramifiedPrimeIdeal_mem_primesOver d hp)

/-- The ramified parity ideal product is fixed by quadratic conjugation. -/
private theorem isAmbiguousIdeal_ramifiedParityIdealProduct
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

private theorem toClassGroup_ramifiedPrimeNarrowClass
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

private theorem classGroup_mk0_sq_eq_one_ramifiedPrimeIdeal
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

private theorem isTotallyPositive_natCast_fractionRing
    {R : Type*} [CommRing R] [IsDomain R] (n : ℕ) (hn : 0 < n) :
    NarrowClassGroup.IsTotallyPositive
      (algebraMap R (FractionRing R) (n : R)) := by
  intro σ
  have hσ : σ (algebraMap R (FractionRing R) (n : R)) = (n : ℝ) := by
    exact map_natCast (σ.comp (algebraMap R (FractionRing R))) n
  rw [hσ]
  exact Nat.cast_pos.mpr hn

private theorem narrowClassGroup_mk0_span_singleton_eq_one_of_isTotallyPositive
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

/-- Quadratic conjugation acts on the narrow ideal class group by inversion. The
point not present in the ordinary class-group statement is positivity: the
principal generator of `I * σ(I)` is the positive integer `absNorm I`. -/
private theorem narrowClassGroup_mk0_map_conjAut_eq_inv
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

private theorem narrowClassGroup_mk0_sq_eq_one_ramifiedPrimeIdeal
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

private noncomputable def ramifiedParityClassProduct
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

private theorem ramifiedParityClassProduct_sq_eq_one
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

private noncomputable def ramifiedParityNarrowClassProduct
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)]
    {p0 : ℕ} (_hp0 : p0 ∈ ramifiedPrimes d)
    (v : ({p // p ∈ (ramifiedPrimes d).erase p0} → Fin 2)) :
    NarrowClassGroup (NumberField.RingOfIntegers (Qsqrtd (d : ℚ))) := by
  classical
  exact Finset.univ.prod fun p =>
    if v p = 0 then 1 else
      ramifiedPrimeNarrowClass d ((Finset.mem_erase.mp p.2).2)

private noncomputable def fullRamifiedParityNarrowClassProduct
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)]
    (v : ({p // p ∈ ramifiedPrimes d} → Fin 2)) :
    NarrowClassGroup (NumberField.RingOfIntegers (Qsqrtd (d : ℚ))) := by
  classical
  exact Finset.univ.prod fun p =>
    if v p = 0 then 1 else ramifiedPrimeNarrowClass d p.2

private theorem mk0_ramifiedParityIdealProduct
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

private theorem mk0_fullRamifiedParityIdealProduct
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

private theorem toClassGroup_ramifiedParityNarrowClassProduct
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

private theorem ramifiedParityNarrowClassProduct_sq_eq_one
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

private theorem fullRamifiedParityNarrowClassProduct_sq_eq_one
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

private theorem narrowClassGroup_mk0_sq_eq_one_ramifiedParityIdealProduct
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)]
    {p0 : ℕ} (hp0 : p0 ∈ ramifiedPrimes d)
    (v : ({p // p ∈ (ramifiedPrimes d).erase p0} → Fin 2)) :
    (NarrowClassGroup.mk0 (ramifiedParityIdealProduct d hp0 v) :
        NarrowClassGroup (NumberField.RingOfIntegers (Qsqrtd (d : ℚ)))) ^ 2 = 1 := by
  rw [mk0_ramifiedParityIdealProduct d hp0 v]
  exact ramifiedParityNarrowClassProduct_sq_eq_one d hp0 v

private theorem card_le_genusBound_of_injective_to_ramifiedParityVectors
    {α : Type*}
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)]
    {p0 : ℕ} (hp0 : p0 ∈ ramifiedPrimes d)
    (f : α → ({p // p ∈ (ramifiedPrimes d).erase p0} → Fin 2))
    (hf : Function.Injective f) :
    Nat.card α ≤ 2 ^ (ramifiedPrimeCount d - 1) := by
  classical
  haveI : Finite α := Finite.of_injective f hf
  have hle : Nat.card α ≤ Nat.card ({p // p ∈ (ramifiedPrimes d).erase p0} → Fin 2) :=
    Nat.card_le_card_of_injective f hf
  refine hle.trans_eq ?_
  rw [Nat.card_eq_fintype_card, Fintype.card_fun]
  have hdomain :
      Fintype.card {p // p ∈ (ramifiedPrimes d).erase p0} =
        ramifiedPrimeCount d - 1 := by
    rw [Fintype.card_coe]
    rw [Finset.card_erase_of_mem hp0]
    rw [ramifiedPrimeCount_eq_card]
  rw [hdomain]
  norm_num

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
private theorem narrowClassGroup_mk0_mul_self_eq_one_of_inversionFixed
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
private theorem exists_integralIdeal_square_principal_relation_of_narrowInversionFixedClass
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
private theorem exists_integralIdeal_square_eq_principal_inverse_of_narrowInversionFixedClass
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

/-- An inversion-fixed narrow class has an integral ideal representative whose
conjugate differs from it by a totally positive principal fractional ideal. This
is the class-level input for the Hilbert-90 adjustment to an ambiguous
representative. -/
private theorem exists_integralIdeal_tp_multiplier_to_conjAut_of_narrowInversionFixedClass
    (K : Type*) [Field K] [NumberField K] [Algebra ℚ K]
    [QuadraticField K] [QuadraticField.Conj K]
    (C : NarrowInversionFixedClass (NumberField.RingOfIntegers K)) :
    ∃ I : (Ideal (NumberField.RingOfIntegers K))⁰,
      NarrowClassGroup.mk0 I = C.1 ∧
        ∃ x : (FractionRing (NumberField.RingOfIntegers K))ˣ,
          NarrowClassGroup.IsTotallyPositive
            (x : FractionRing (NumberField.RingOfIntegers K)) ∧
            FractionalIdeal.mk0 (FractionRing (NumberField.RingOfIntegers K)) I *
                toPrincipalIdeal (NumberField.RingOfIntegers K)
                  (FractionRing (NumberField.RingOfIntegers K)) x =
              FractionalIdeal.mk0 (FractionRing (NumberField.RingOfIntegers K))
                (conjAutNonzeroIdealMulEquiv K I) := by
  obtain ⟨I, hI⟩ := NarrowClassGroup.mk0_surjective C.1
  refine ⟨I, hI, ?_⟩
  have hconj :
      NarrowClassGroup.mk0 (conjAutNonzeroIdealMulEquiv K I) = C.1 := by
    calc
      NarrowClassGroup.mk0 (conjAutNonzeroIdealMulEquiv K I) =
          (NarrowClassGroup.mk0 I)⁻¹ :=
        narrowClassGroup_mk0_map_conjAut_eq_inv K I
      _ = C.1⁻¹ := by rw [hI]
      _ = C.1 := C.2.symm
  exact (NarrowClassGroup.mk0_eq_mk0_iff_exists_fraction_ring).mp (hI.trans hconj.symm)

/-- A totally positive fraction-field unit in `Q(√d)` has nonnegative field norm
after transport to the standard field model. -/
private theorem algebra_norm_nonneg_of_isTotallyPositive_fractionRing_algEquiv_qsqrtd
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)]
    {x : (FractionRing (NumberField.RingOfIntegers (Qsqrtd (d : ℚ))))ˣ}
    (hxpos : NarrowClassGroup.IsTotallyPositive
      (x : FractionRing (NumberField.RingOfIntegers (Qsqrtd (d : ℚ))))) :
    0 ≤ Algebra.norm ℚ
      (FractionRing.algEquiv (NumberField.RingOfIntegers (Qsqrtd (d : ℚ)))
        (Qsqrtd (d : ℚ))
        (x : FractionRing (NumberField.RingOfIntegers (Qsqrtd (d : ℚ))))) := by
  let R := NumberField.RingOfIntegers (Qsqrtd (d : ℚ))
  let e : FractionRing R ≃ₐ[R] Qsqrtd (d : ℚ) :=
    FractionRing.algEquiv R (Qsqrtd (d : ℚ))
  let z : Qsqrtd (d : ℚ) := e (x : FractionRing R)
  change 0 ≤ Algebra.norm ℚ z
  rw [Qsqrtd.algebraNorm_eq_qsqrtdNorm]
  by_cases hdneg : d < 0
  · exact Qsqrtd.norm_nonneg_of_neg hdneg z
  have hd_ne_zero : d ≠ 0 := Squarefree.ne_zero (Fact.out : Squarefree d)
  have hdpos : 0 < d := by omega
  have hd_nonneg_real : 0 ≤ (d : ℝ) := by exact_mod_cast le_of_lt hdpos
  let σpos : FractionRing R →+* ℝ :=
    (Qsqrtd.realEmbeddingPos d hd_nonneg_real).toRingHom.comp e.toRingHom
  let σneg : FractionRing R →+* ℝ :=
    (Qsqrtd.realEmbeddingNeg d hd_nonneg_real).toRingHom.comp e.toRingHom
  have hpos_pos : 0 < Qsqrtd.realEmbeddingPos d hd_nonneg_real z := by
    simpa [σpos, z, e, R] using hxpos σpos
  have hpos_neg : 0 < Qsqrtd.realEmbeddingNeg d hd_nonneg_real z := by
    simpa [σneg, z, e, R] using hxpos σneg
  have hnorm_pos_real : 0 < (Qsqrtd.norm z : ℝ) :=
    Qsqrtd.norm_pos_of_realEmbedding_pos d hd_nonneg_real hpos_pos hpos_neg
  have hnorm_pos_rat : 0 < Qsqrtd.norm z := by
    exact_mod_cast hnorm_pos_real
  exact le_of_lt hnorm_pos_rat

/-- Norm-one extraction boundary. A totally positive principal multiplier
relating an ideal to its conjugate has field norm `1`. -/
private theorem norm_eq_one_of_tp_multiplier_to_conjAut
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)]
    (I : (Ideal (NumberField.RingOfIntegers (Qsqrtd (d : ℚ))))⁰)
    {x : (FractionRing (NumberField.RingOfIntegers (Qsqrtd (d : ℚ))))ˣ}
    (hxpos : NarrowClassGroup.IsTotallyPositive
      (x : FractionRing (NumberField.RingOfIntegers (Qsqrtd (d : ℚ)))))
    (hconj :
      FractionalIdeal.mk0
          (FractionRing (NumberField.RingOfIntegers (Qsqrtd (d : ℚ)))) I *
          toPrincipalIdeal (NumberField.RingOfIntegers (Qsqrtd (d : ℚ)))
            (FractionRing (NumberField.RingOfIntegers (Qsqrtd (d : ℚ)))) x =
        FractionalIdeal.mk0
          (FractionRing (NumberField.RingOfIntegers (Qsqrtd (d : ℚ))))
          (conjAutNonzeroIdealMulEquiv (Qsqrtd (d : ℚ)) I)) :
    Algebra.norm ℚ
      (FractionRing.algEquiv (NumberField.RingOfIntegers (Qsqrtd (d : ℚ)))
        (Qsqrtd (d : ℚ))
        (x : FractionRing (NumberField.RingOfIntegers (Qsqrtd (d : ℚ))))) = 1 := by
  let R := NumberField.RingOfIntegers (Qsqrtd (d : ℚ))
  let e := FractionRing.algEquiv R (Qsqrtd (d : ℚ))
  have habs_map :
      Ideal.absNorm
          (Ideal.map (conjAutRingOfIntegers (Qsqrtd (d : ℚ)) : R →+* R)
            (I : Ideal R)) =
        Ideal.absNorm (I : Ideal R) := by
    exact Ideal.absNorm_map_equiv (conjAutRingOfIntegers (Qsqrtd (d : ℚ))) (I : Ideal R)
  have habs_map_rat :
      (Ideal.absNorm
          (Ideal.map (conjAutRingOfIntegers (Qsqrtd (d : ℚ)) : R →+* R)
            (I : Ideal R)) : ℚ) =
        Ideal.absNorm (I : Ideal R) := by
    exact_mod_cast habs_map
  have hnorm_abs : |Algebra.norm ℚ (e (x : FractionRing R))| = 1 := by
    let E := FractionalIdeal.canonicalEquiv R⁰ (FractionRing R) (Qsqrtd (d : ℚ))
    have h :=
      congrArg
        (fun J : (FractionalIdeal R⁰ (FractionRing R))ˣ =>
          FractionalIdeal.absNorm (E (J : FractionalIdeal R⁰ (FractionRing R))))
        hconj
    have hIpos :
        (0 : ℚ) < Ideal.absNorm (I : Ideal R) := by
      exact_mod_cast Ideal.absNorm_pos_of_nonZeroDivisors I
    have hIne : (Ideal.absNorm (I : Ideal R) : ℚ) ≠ 0 := ne_of_gt hIpos
    have h' :
        (Ideal.absNorm (I : Ideal R) : ℚ) *
            |Algebra.norm ℚ (e (x : FractionRing R))| =
          (Ideal.absNorm (I : Ideal R) : ℚ) := by
      change
        FractionalIdeal.absNorm
            (E (((FractionalIdeal.mk0 (FractionRing R) I) *
              toPrincipalIdeal R (FractionRing R) x :
                (FractionalIdeal R⁰ (FractionRing R))ˣ) :
              FractionalIdeal R⁰ (FractionRing R))) =
          FractionalIdeal.absNorm
            (E ((FractionalIdeal.mk0 (FractionRing R)
                (conjAutNonzeroIdealMulEquiv (Qsqrtd (d : ℚ)) I) :
                  (FractionalIdeal R⁰ (FractionRing R))ˣ) :
              FractionalIdeal R⁰ (FractionRing R))) at h
      rw [Units.val_mul, map_mul, FractionalIdeal.absNorm.map_mul] at h
      simpa [R, e, E, FractionalIdeal.coe_mk0, FractionalIdeal.coeIdeal_absNorm,
        coe_toPrincipalIdeal, FractionalIdeal.canonicalEquiv_spanSingleton,
        FractionalIdeal.absNorm_span_singleton, coe_conjAutNonzeroIdealMulEquiv_apply,
        habs_map_rat] using h
    exact mul_left_cancel₀ hIne (by simpa using h')
  have hnorm_nonneg : 0 ≤ Algebra.norm ℚ (e (x : FractionRing R)) := by
    exact algebra_norm_nonneg_of_isTotallyPositive_fractionRing_algEquiv_qsqrtd d hxpos
  have hnorm_abs_self :
      |Algebra.norm ℚ (e (x : FractionRing R))| = Algebra.norm ℚ (e (x : FractionRing R)) :=
    abs_of_nonneg hnorm_nonneg
  rw [hnorm_abs_self] at hnorm_abs
  exact hnorm_abs

/-- Fraction-field Hilbert 90 for the localized conjugation action. A norm-one
fraction-field unit is an ordinary conjugation coboundary.

This private helper is universe-zero because the available mathlib Hilbert 90
theorem is universe-zero; this is enough for the `Qsqrtd` application below. -/
private theorem exists_conjAut_coboundary_of_norm_eq_one
    (K : Type) [Field K] [NumberField K] [Algebra ℚ K]
    [QuadraticField K] [QuadraticField.Conj K]
    {x : (FractionRing (NumberField.RingOfIntegers K))ˣ}
    (hxnorm :
      Algebra.norm ℚ
        (FractionRing.algEquiv (NumberField.RingOfIntegers K) K
          (x : FractionRing (NumberField.RingOfIntegers K))) = 1) :
    ∃ y : (FractionRing (NumberField.RingOfIntegers K))ˣ,
      x = y * (Units.mapEquiv (conjAutFractionRingAlgEquiv K).toRingEquiv y)⁻¹ := by
  let R := NumberField.RingOfIntegers K
  let e := FractionRing.algEquiv R K
  haveI : IsGalois ℚ K := Algebra.IsQuadraticExtension.isGalois ℚ K
  have hcard : Nat.card Gal(K / ℚ) = 2 := by
    rw [IsGalois.card_aut_eq_finrank, Algebra.IsQuadraticExtension.finrank_eq_two]
  haveI : IsCyclic Gal(K / ℚ) := isCyclic_of_prime_card hcard
  have hconj_ne_one : (QuadraticField.conjAut K : Gal(K / ℚ)) ≠ 1 := by
    simpa using (QuadraticField.Conj.conj_ne_refl (K := K))
  have hg : ∀ σ : Gal(K / ℚ), σ ∈ Subgroup.zpowers (QuadraticField.conjAut K) := by
    intro σ
    exact mem_zpowers_of_prime_card (p := 2) hcard hconj_ne_one
  obtain ⟨yK, hyK⟩ :=
    groupCohomology.exists_div_of_norm_eq_one
      (K := ℚ) (L := K) (g := QuadraticField.conjAut K) hg hxnorm
  let y : (FractionRing R)ˣ := Units.mapEquiv e.symm.toRingEquiv yK
  refine ⟨y, ?_⟩
  apply Units.ext
  apply e.injective
  have hy_map : e (y : FractionRing R) = (yK : K) := by
    change e (e.symm (yK : K)) = (yK : K)
    exact e.apply_symm_apply (yK : K)
  have hσ_map :
      e (((Units.mapEquiv (conjAutFractionRingAlgEquiv K).toRingEquiv y) :
          (FractionRing R)ˣ) : FractionRing R) =
        QuadraticField.conjAut K (yK : K) := by
    calc
      e (((Units.mapEquiv (conjAutFractionRingAlgEquiv K).toRingEquiv y) :
          (FractionRing R)ˣ) : FractionRing R) =
          e ((conjAutFractionRingAlgEquiv K) (y : FractionRing R)) := rfl
      _ = QuadraticField.conjAut K (e (y : FractionRing R)) := by
        change FractionRing.algEquiv (NumberField.RingOfIntegers K) K
            ((conjAutFractionRingAlgEquiv K) (y : FractionRing R)) =
          QuadraticField.conjAut K
            (FractionRing.algEquiv (NumberField.RingOfIntegers K) K (y : FractionRing R))
        exact fractionRing_algEquiv_conjAutFractionRingAlgEquiv K (y : FractionRing R)
      _ = QuadraticField.conjAut K (yK : K) := by
        rw [hy_map]
  calc
    e (x : FractionRing R) = (yK : K) / QuadraticField.conjAut K (yK : K) := hyK.symm
    _ =
        e (y : FractionRing R) *
          (e (((Units.mapEquiv (conjAutFractionRingAlgEquiv K).toRingEquiv y) :
            (FractionRing R)ˣ) : FractionRing R))⁻¹ := by
      rw [hy_map, hσ_map]
      exact div_eq_mul_inv (yK : K) (QuadraticField.conjAut K (yK : K))
    _ = e ((y * (Units.mapEquiv (conjAutFractionRingAlgEquiv K).toRingEquiv y)⁻¹ :
          (FractionRing R)ˣ) : FractionRing R) := by
      dsimp
      simp

/-- Hilbert-90 extraction boundary. A principal multiplier relating an ideal to
its conjugate should be an ordinary conjugation coboundary in the fraction
field. -/
private theorem exists_conjAut_coboundary_of_tp_multiplier_to_conjAut
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)]
    (I : (Ideal (NumberField.RingOfIntegers (Qsqrtd (d : ℚ))))⁰)
    {x : (FractionRing (NumberField.RingOfIntegers (Qsqrtd (d : ℚ))))ˣ}
    (hxpos : NarrowClassGroup.IsTotallyPositive
      (x : FractionRing (NumberField.RingOfIntegers (Qsqrtd (d : ℚ)))))
    (hconj :
      FractionalIdeal.mk0
          (FractionRing (NumberField.RingOfIntegers (Qsqrtd (d : ℚ)))) I *
          toPrincipalIdeal (NumberField.RingOfIntegers (Qsqrtd (d : ℚ)))
            (FractionRing (NumberField.RingOfIntegers (Qsqrtd (d : ℚ)))) x =
        FractionalIdeal.mk0
          (FractionRing (NumberField.RingOfIntegers (Qsqrtd (d : ℚ))))
          (conjAutNonzeroIdealMulEquiv (Qsqrtd (d : ℚ)) I)) :
    ∃ y : (FractionRing (NumberField.RingOfIntegers (Qsqrtd (d : ℚ))))ˣ,
      x =
        y * (Units.mapEquiv (conjAutFractionRingAlgEquiv (Qsqrtd (d : ℚ))).toRingEquiv y)⁻¹ := by
  exact exists_conjAut_coboundary_of_norm_eq_one (Qsqrtd (d : ℚ))
    (norm_eq_one_of_tp_multiplier_to_conjAut d I hxpos hconj)

/-- A real embedding of `Q(√d)` sends the standard square root to one of the
two real roots. -/
private theorem qsqrt_algHom_omega_eq_sqrt_or_neg
    (d : ℤ) (φ : Qsqrtd (d : ℚ) →ₐ[ℚ] ℝ) :
    φ QuadraticAlgebra.omega = Real.sqrt (d : ℝ) ∨
      φ QuadraticAlgebra.omega = -Real.sqrt (d : ℝ) := by
  have hsq :
      φ QuadraticAlgebra.omega * φ QuadraticAlgebra.omega = (d : ℝ) := by
    have h :=
      congrArg φ
        (QuadraticAlgebra.omega_mul_omega_eq_add (R := ℚ) (a := (d : ℚ)) (b := 0))
    simpa [Algebra.smul_def] using h
  have hsq' : φ QuadraticAlgebra.omega ^ 2 = (d : ℝ) := by
    simpa [sq] using hsq
  have habs : |φ QuadraticAlgebra.omega| = Real.sqrt (d : ℝ) := by
    rw [← Real.sqrt_sq_eq_abs (φ QuadraticAlgebra.omega), hsq']
  rcases abs_cases (φ QuadraticAlgebra.omega) with h | h
  · left
    linarith
  · right
    linarith

/-- The two explicit real embeddings exhaust the real embeddings of `Q(√d)`. -/
private theorem qsqrt_algHom_eq_realEmbeddingPos_or_neg
    (d : ℤ) (hd : 0 ≤ (d : ℝ)) (φ : Qsqrtd (d : ℚ) →ₐ[ℚ] ℝ) :
    φ = Qsqrtd.realEmbeddingPos d hd ∨ φ = Qsqrtd.realEmbeddingNeg d hd := by
  rcases qsqrt_algHom_omega_eq_sqrt_or_neg d φ with hω | hω
  · left
    apply QuadraticAlgebra.algHom_ext
    change φ QuadraticAlgebra.omega = Qsqrtd.realEmbeddingPos d hd QuadraticAlgebra.omega
    rw [hω, Qsqrtd.realEmbeddingPos_apply]
    simp
  · right
    apply QuadraticAlgebra.algHom_ext
    change φ QuadraticAlgebra.omega = Qsqrtd.realEmbeddingNeg d hd QuadraticAlgebra.omega
    rw [hω, Qsqrtd.realEmbeddingNeg_apply]
    simp

private theorem qsqrt_realEmbeddingPos_conjAut
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)]
    (hd : 0 ≤ (d : ℝ)) (z : Qsqrtd (d : ℚ)) :
    Qsqrtd.realEmbeddingPos d hd (QuadraticField.conjAut (Qsqrtd (d : ℚ)) z) =
      Qsqrtd.realEmbeddingNeg d hd z := by
  rw [show QuadraticField.conjAut (Qsqrtd (d : ℚ)) z = star z from rfl]
  rw [Qsqrtd.realEmbeddingPos_apply, Qsqrtd.realEmbeddingNeg_apply]
  simp [QuadraticAlgebra.re_star, QuadraticAlgebra.im_star]
  ring

private theorem qsqrt_ringHom_eval_eq_algHom_eval
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)]
    (σ : FractionRing (NumberField.RingOfIntegers (Qsqrtd (d : ℚ))) →+* ℝ)
    (w : FractionRing (NumberField.RingOfIntegers (Qsqrtd (d : ℚ)))) :
    let R := NumberField.RingOfIntegers (Qsqrtd (d : ℚ))
    let e : FractionRing R ≃ₐ[R] Qsqrtd (d : ℚ) :=
      FractionRing.algEquiv R (Qsqrtd (d : ℚ))
    let φ : Qsqrtd (d : ℚ) →ₐ[ℚ] ℝ := (σ.comp e.symm.toRingHom).toRatAlgHom
    σ w = φ (e w) := by
  intro R e φ
  dsimp [φ]
  have hw : e.toRingEquiv.symm (e w) = w := by
    exact e.toRingEquiv.symm_apply_apply w
  rw [hw]

/-- Sign choice for the quadratic Hilbert-90 representative in the standard
model. If a totally positive element is written as `y / σ(y)`, then either `y`
or `-y` is totally positive. -/
private theorem qsqrt_isTotallyPositive_or_neg_isTotallyPositive_of_totallyPositive_coboundary
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)]
    {x y : (FractionRing (NumberField.RingOfIntegers (Qsqrtd (d : ℚ))))ˣ}
    (hxpos : NarrowClassGroup.IsTotallyPositive
      (x : FractionRing (NumberField.RingOfIntegers (Qsqrtd (d : ℚ)))))
    (hy :
      x =
        y * (Units.mapEquiv (conjAutFractionRingAlgEquiv (Qsqrtd (d : ℚ))).toRingEquiv y)⁻¹) :
    NarrowClassGroup.IsTotallyPositive
        (y : FractionRing (NumberField.RingOfIntegers (Qsqrtd (d : ℚ)))) ∨
      NarrowClassGroup.IsTotallyPositive
        ((-y : (FractionRing (NumberField.RingOfIntegers (Qsqrtd (d : ℚ))))ˣ) :
          FractionRing (NumberField.RingOfIntegers (Qsqrtd (d : ℚ)))) := by
  by_cases hreal :
      Nonempty (FractionRing (NumberField.RingOfIntegers (Qsqrtd (d : ℚ))) →+* ℝ)
  · let R := NumberField.RingOfIntegers (Qsqrtd (d : ℚ))
    let e : FractionRing R ≃ₐ[R] Qsqrtd (d : ℚ) :=
      FractionRing.algEquiv R (Qsqrtd (d : ℚ))
    let z : Qsqrtd (d : ℚ) := e (y : FractionRing R)
    let τy : (FractionRing R)ˣ :=
      Units.mapEquiv (conjAutFractionRingAlgEquiv (Qsqrtd (d : ℚ))).toRingEquiv y
    have hd_nonneg_real : 0 ≤ (d : ℝ) := by
      by_contra hdn
      have hdneg : d < 0 := by
        have : (d : ℝ) < 0 := lt_of_not_ge hdn
        exact_mod_cast this
      haveI : IsEmpty (FractionRing (NumberField.RingOfIntegers (Qsqrtd (d : ℚ))) →+* ℝ) :=
        Qsqrtd.Imaginary.isEmpty_fractionRing_realEmbeddings d hdneg
      rcases hreal with ⟨σ⟩
      exact isEmptyElim σ
    let σpos : FractionRing R →+* ℝ :=
      (Qsqrtd.realEmbeddingPos d hd_nonneg_real).toRingHom.comp e.toRingHom
    have hσpos_y :
        σpos (y : FractionRing R) = Qsqrtd.realEmbeddingPos d hd_nonneg_real z := rfl
    have hσpos_τy :
        σpos (τy : FractionRing R) = Qsqrtd.realEmbeddingNeg d hd_nonneg_real z := by
      calc
        σpos (τy : FractionRing R) =
            Qsqrtd.realEmbeddingPos d hd_nonneg_real
              (e ((conjAutFractionRingAlgEquiv (Qsqrtd (d : ℚ)))
                (y : FractionRing R))) := rfl
        _ =
            Qsqrtd.realEmbeddingPos d hd_nonneg_real
              (QuadraticField.conjAut (Qsqrtd (d : ℚ)) (e (y : FractionRing R))) := by
          rw [fractionRing_algEquiv_conjAutFractionRingAlgEquiv]
        _ = Qsqrtd.realEmbeddingNeg d hd_nonneg_real z := by
          simpa [z] using qsqrt_realEmbeddingPos_conjAut d hd_nonneg_real z
    have hratio :
        0 <
          Qsqrtd.realEmbeddingPos d hd_nonneg_real z /
            Qsqrtd.realEmbeddingNeg d hd_nonneg_real z := by
      have hxσ := hxpos σpos
      rw [hy] at hxσ
      change 0 < σpos ((y * τy⁻¹ : (FractionRing R)ˣ) : FractionRing R) at hxσ
      simpa [div_eq_mul_inv, hσpos_y, hσpos_τy] using hxσ
    rcases div_pos_iff.mp hratio with hsign | hsign
    · left
      intro σ
      let φ : Qsqrtd (d : ℚ) →ₐ[ℚ] ℝ :=
        (σ.comp e.symm.toRingHom).toRatAlgHom
      have hσy :
          σ (y : FractionRing R) = φ (e (y : FractionRing R)) :=
        qsqrt_ringHom_eval_eq_algHom_eval d σ (y : FractionRing R)
      rcases qsqrt_algHom_eq_realEmbeddingPos_or_neg d hd_nonneg_real φ with hφ | hφ
      · rw [hσy, hφ]
        simpa [z] using hsign.1
      · rw [hσy, hφ]
        simpa [z] using hsign.2
    · right
      intro σ
      let φ : Qsqrtd (d : ℚ) →ₐ[ℚ] ℝ :=
        (σ.comp e.symm.toRingHom).toRatAlgHom
      have hσy :
          σ (y : FractionRing R) = φ (e (y : FractionRing R)) :=
        qsqrt_ringHom_eval_eq_algHom_eval d σ (y : FractionRing R)
      rcases qsqrt_algHom_eq_realEmbeddingPos_or_neg d hd_nonneg_real φ with hφ | hφ
      · have hyneg : σ (y : FractionRing R) < 0 := by
          rw [hσy, hφ]
          simpa [z] using hsign.1
        simpa using neg_pos.mpr hyneg
      · have hyneg : σ (y : FractionRing R) < 0 := by
          rw [hσy, hφ]
          simpa [z] using hsign.2
        simpa using neg_pos.mpr hyneg
  · left
    intro σ
    exact False.elim (hreal ⟨σ⟩)

/-- Positivity adjustment boundary for the quadratic Hilbert-90 coboundary. If a
totally positive multiplier is an ordinary conjugation coboundary, the
coboundary representative can be chosen totally positive. -/
private theorem exists_totallyPositive_conjAut_coboundary_of_conjAut_coboundary
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)]
    {x y : (FractionRing (NumberField.RingOfIntegers (Qsqrtd (d : ℚ))))ˣ}
    (hxpos : NarrowClassGroup.IsTotallyPositive
      (x : FractionRing (NumberField.RingOfIntegers (Qsqrtd (d : ℚ)))))
    (hy :
      x =
        y * (Units.mapEquiv (conjAutFractionRingAlgEquiv (Qsqrtd (d : ℚ))).toRingEquiv y)⁻¹) :
    ∃ z : (FractionRing (NumberField.RingOfIntegers (Qsqrtd (d : ℚ))))ˣ,
      NarrowClassGroup.IsTotallyPositive
        (z : FractionRing (NumberField.RingOfIntegers (Qsqrtd (d : ℚ)))) ∧
        x =
          z *
            (Units.mapEquiv
              (conjAutFractionRingAlgEquiv (Qsqrtd (d : ℚ))).toRingEquiv z)⁻¹ := by
  obtain hypos | hyneg :=
    qsqrt_isTotallyPositive_or_neg_isTotallyPositive_of_totallyPositive_coboundary d hxpos hy
  · exact ⟨y, hypos, hy⟩
  · refine ⟨-y, hyneg, ?_⟩
    let R := NumberField.RingOfIntegers (Qsqrtd (d : ℚ))
    let σy :=
      Units.mapEquiv
        ((conjAutFractionRingAlgEquiv (Qsqrtd (d : ℚ))).toRingEquiv :
          FractionRing R ≃* FractionRing R) y
    have hmap_neg :
        Units.mapEquiv
            (conjAutFractionRingAlgEquiv (Qsqrtd (d : ℚ))).toRingEquiv (-y) =
          -σy := by
      ext
      simp [σy]
    calc
      x =
          y *
            (Units.mapEquiv
              (conjAutFractionRingAlgEquiv (Qsqrtd (d : ℚ))).toRingEquiv y)⁻¹ := hy
      _ =
          (-y) *
            (Units.mapEquiv
              (conjAutFractionRingAlgEquiv (Qsqrtd (d : ℚ))).toRingEquiv (-y))⁻¹ := by
        rw [hmap_neg]
        simp [σy]

/-- Narrow Hilbert-90 boundary. A totally positive principal multiplier relating
an ideal to its conjugate should be a totally positive conjugation coboundary. -/
private theorem exists_totallyPositive_conjAut_coboundary_of_tp_multiplier_to_conjAut
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)]
    (I : (Ideal (NumberField.RingOfIntegers (Qsqrtd (d : ℚ))))⁰)
    {x : (FractionRing (NumberField.RingOfIntegers (Qsqrtd (d : ℚ))))ˣ}
    (hxpos : NarrowClassGroup.IsTotallyPositive
      (x : FractionRing (NumberField.RingOfIntegers (Qsqrtd (d : ℚ)))))
    (hconj :
      FractionalIdeal.mk0
          (FractionRing (NumberField.RingOfIntegers (Qsqrtd (d : ℚ)))) I *
          toPrincipalIdeal (NumberField.RingOfIntegers (Qsqrtd (d : ℚ)))
            (FractionRing (NumberField.RingOfIntegers (Qsqrtd (d : ℚ)))) x =
        FractionalIdeal.mk0
          (FractionRing (NumberField.RingOfIntegers (Qsqrtd (d : ℚ))))
          (conjAutNonzeroIdealMulEquiv (Qsqrtd (d : ℚ)) I)) :
    ∃ y : (FractionRing (NumberField.RingOfIntegers (Qsqrtd (d : ℚ))))ˣ,
      NarrowClassGroup.IsTotallyPositive
        (y : FractionRing (NumberField.RingOfIntegers (Qsqrtd (d : ℚ)))) ∧
        x =
          y *
            (Units.mapEquiv
              (conjAutFractionRingAlgEquiv (Qsqrtd (d : ℚ))).toRingEquiv y)⁻¹ := by
  obtain ⟨y, hy⟩ :=
    exists_conjAut_coboundary_of_tp_multiplier_to_conjAut d I hxpos hconj
  exact exists_totallyPositive_conjAut_coboundary_of_conjAut_coboundary d hxpos hy

/-- A coboundary multiplier turns the relation `I * (x) = σ(I)` into the
fractional-ideal equality `I * (y) = σ(I) * (σ y)`. -/
private theorem fractionalRep_eq_conjAutFractionalRep_of_coboundary
    (K : Type*) [Field K] [NumberField K] [Algebra ℚ K]
    [QuadraticField K] [QuadraticField.Conj K]
    (I : (Ideal (NumberField.RingOfIntegers K))⁰)
    {x y : (FractionRing (NumberField.RingOfIntegers K))ˣ}
    (hy :
      x = y * (Units.mapEquiv (conjAutFractionRingAlgEquiv K).toRingEquiv y)⁻¹)
    (hconj :
      FractionalIdeal.mk0 (FractionRing (NumberField.RingOfIntegers K)) I *
          toPrincipalIdeal (NumberField.RingOfIntegers K)
            (FractionRing (NumberField.RingOfIntegers K)) x =
        FractionalIdeal.mk0 (FractionRing (NumberField.RingOfIntegers K))
          (conjAutNonzeroIdealMulEquiv K I)) :
    FractionalIdeal.mk0 (FractionRing (NumberField.RingOfIntegers K)) I *
        toPrincipalIdeal (NumberField.RingOfIntegers K)
          (FractionRing (NumberField.RingOfIntegers K)) y =
      FractionalIdeal.mk0 (FractionRing (NumberField.RingOfIntegers K))
          (conjAutNonzeroIdealMulEquiv K I) *
        toPrincipalIdeal (NumberField.RingOfIntegers K)
          (FractionRing (NumberField.RingOfIntegers K))
          (Units.mapEquiv (conjAutFractionRingAlgEquiv K).toRingEquiv y) := by
  let R := NumberField.RingOfIntegers K
  let σy : (FractionRing R)ˣ :=
    Units.mapEquiv
      ((conjAutFractionRingAlgEquiv K).toRingEquiv : FractionRing R ≃* FractionRing R) y
  have hxy : x * σy = y := by
    calc
      x * σy = (y * σy⁻¹) * σy := by
        rw [hy]
      _ = y * (σy⁻¹ * σy) := by
        rw [mul_assoc]
      _ = y := by
        rw [inv_mul_cancel, mul_one]
  calc
    FractionalIdeal.mk0 (FractionRing R) I * toPrincipalIdeal R (FractionRing R) y =
        FractionalIdeal.mk0 (FractionRing R) I *
          toPrincipalIdeal R (FractionRing R) (x * σy) := by
      rw [hxy]
    _ =
        FractionalIdeal.mk0 (FractionRing R) I *
          (toPrincipalIdeal R (FractionRing R) x * toPrincipalIdeal R (FractionRing R) σy) := by
      rw [map_mul]
    _ =
        (FractionalIdeal.mk0 (FractionRing R) I * toPrincipalIdeal R (FractionRing R) x) *
          toPrincipalIdeal R (FractionRing R) σy := by
      rw [mul_assoc]
    _ =
        FractionalIdeal.mk0 (FractionRing R) (conjAutNonzeroIdealMulEquiv K I) *
          toPrincipalIdeal R (FractionRing R) σy := by
      rw [hconj]

/-- The base-ring-equivalence image of an integral fractional representative is
the fractional representative of the conjugate integral ideal. -/
private theorem ringEquivMap_conjAut_mk0
    (K : Type*) [Field K] [NumberField K] [Algebra ℚ K]
    [QuadraticField K] [QuadraticField.Conj K]
    (I : (Ideal (NumberField.RingOfIntegers K))⁰) :
    FractionalIdeal.ringEquivMap
        (K := FractionRing (NumberField.RingOfIntegers K))
        (L := FractionRing (NumberField.RingOfIntegers K))
        (conjAutRingOfIntegers K)
        (FractionalIdeal.mk0 (FractionRing (NumberField.RingOfIntegers K)) I) =
      FractionalIdeal.mk0 (FractionRing (NumberField.RingOfIntegers K))
        (conjAutNonzeroIdealMulEquiv K I) := by
  let R := NumberField.RingOfIntegers K
  change
    FractionalIdeal.ringEquivMap
        (K := FractionRing R) (L := FractionRing R)
        (conjAutRingOfIntegers K)
        ((I : Ideal R) : FractionalIdeal R⁰ (FractionRing R)) =
      (((conjAutNonzeroIdealMulEquiv K I : (Ideal R)⁰) : Ideal R) :
        FractionalIdeal R⁰ (FractionRing R))
  rw [FractionalIdeal.ringEquivMap_coeIdeal]
  simp [coe_conjAutNonzeroIdealMulEquiv_apply]

/-- The base-ring-equivalence image of a principal fractional ideal generated by
`y` is the principal fractional ideal generated by the conjugate of `y`. -/
private theorem ringEquivMap_conjAut_toPrincipalIdeal
    (K : Type*) [Field K] [NumberField K] [Algebra ℚ K]
    [QuadraticField K] [QuadraticField.Conj K]
    (y : (FractionRing (NumberField.RingOfIntegers K))ˣ) :
    FractionalIdeal.ringEquivMap
        (K := FractionRing (NumberField.RingOfIntegers K))
        (L := FractionRing (NumberField.RingOfIntegers K))
        (conjAutRingOfIntegers K)
        (toPrincipalIdeal (NumberField.RingOfIntegers K)
          (FractionRing (NumberField.RingOfIntegers K)) y :
            FractionalIdeal (NumberField.RingOfIntegers K)⁰
              (FractionRing (NumberField.RingOfIntegers K))) =
      (toPrincipalIdeal (NumberField.RingOfIntegers K)
        (FractionRing (NumberField.RingOfIntegers K))
        (Units.mapEquiv (conjAutFractionRingAlgEquiv K).toRingEquiv y) :
          FractionalIdeal (NumberField.RingOfIntegers K)⁰
            (FractionRing (NumberField.RingOfIntegers K))) := by
  let R := NumberField.RingOfIntegers K
  rw [coe_toPrincipalIdeal, coe_toPrincipalIdeal, FractionalIdeal.ringEquivMap_spanSingleton]
  rfl

/-- Rephrase the explicit conjugate-factorization equality as fixedness under
the fractional-ideal map induced by ring-of-integers conjugation. -/
private theorem ringEquivMap_conjAut_fractionalRep_eq_self_of_eq_conjAutFractionalRep
    (K : Type*) [Field K] [NumberField K] [Algebra ℚ K]
    [QuadraticField K] [QuadraticField.Conj K]
    (I : (Ideal (NumberField.RingOfIntegers K))⁰)
    (y : (FractionRing (NumberField.RingOfIntegers K))ˣ)
    (hfixed :
      FractionalIdeal.mk0 (FractionRing (NumberField.RingOfIntegers K)) I *
          toPrincipalIdeal (NumberField.RingOfIntegers K)
            (FractionRing (NumberField.RingOfIntegers K)) y =
        FractionalIdeal.mk0 (FractionRing (NumberField.RingOfIntegers K))
            (conjAutNonzeroIdealMulEquiv K I) *
          toPrincipalIdeal (NumberField.RingOfIntegers K)
            (FractionRing (NumberField.RingOfIntegers K))
            (Units.mapEquiv (conjAutFractionRingAlgEquiv K).toRingEquiv y)) :
    FractionalIdeal.ringEquivMap
        (K := FractionRing (NumberField.RingOfIntegers K))
        (L := FractionRing (NumberField.RingOfIntegers K))
        (conjAutRingOfIntegers K)
        (FractionalIdeal.mk0 (FractionRing (NumberField.RingOfIntegers K)) I *
          toPrincipalIdeal (NumberField.RingOfIntegers K)
            (FractionRing (NumberField.RingOfIntegers K)) y) =
      FractionalIdeal.mk0 (FractionRing (NumberField.RingOfIntegers K)) I *
        toPrincipalIdeal (NumberField.RingOfIntegers K)
          (FractionRing (NumberField.RingOfIntegers K)) y := by
  let R := NumberField.RingOfIntegers K
  rw [FractionalIdeal.ringEquivMap_mul, ringEquivMap_conjAut_mk0,
    ringEquivMap_conjAut_toPrincipalIdeal]
  exact (congrArg Units.val hfixed).symm

/-- A denominator-cleared integral representative using a conjugation-invariant
square denominator. If `a` is a denominator for `F`, this is
`(a * σ a ^ 2) * F.num`, whose associated fractional ideal is
`(a * σ a)^2 * F`. -/
private noncomputable def conjInvariantIntegralRep
    (K : Type*) [Field K] [NumberField K] [Algebra ℚ K]
    [QuadraticField K] [QuadraticField.Conj K]
    (F : FractionalIdeal (NumberField.RingOfIntegers K)⁰
      (FractionRing (NumberField.RingOfIntegers K))) :
    Ideal (NumberField.RingOfIntegers K) :=
  let a : NumberField.RingOfIntegers K := F.den
  let b : NumberField.RingOfIntegers K := conjAutRingOfIntegers K a
  Ideal.span ({a * b ^ 2} : Set (NumberField.RingOfIntegers K)) * F.num

private theorem conjInvariantIntegralRep_mem_nonZeroDivisors
    (K : Type*) [Field K] [NumberField K] [Algebra ℚ K]
    [QuadraticField K] [QuadraticField.Conj K]
    {F : FractionalIdeal (NumberField.RingOfIntegers K)⁰
      (FractionRing (NumberField.RingOfIntegers K))}
    (hF : F ≠ 0) :
    conjInvariantIntegralRep K F ∈ (Ideal (NumberField.RingOfIntegers K))⁰ := by
  let R := NumberField.RingOfIntegers K
  let a : R := F.den
  let b : R := conjAutRingOfIntegers K a
  have ha0 : a ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp F.den.prop
  have hb0 : b ≠ 0 := by
    dsimp [b]
    intro hb
    exact ha0 ((conjAutRingOfIntegers K).injective (by simpa using hb))
  rw [mem_nonZeroDivisors_iff_ne_zero, conjInvariantIntegralRep]
  dsimp [a, b]
  apply mul_ne_zero
  · rw [Ideal.zero_eq_bot, ne_eq, Ideal.span_singleton_eq_bot]
    exact mul_ne_zero ha0 (pow_ne_zero 2 hb0)
  · rwa [ne_eq, FractionalIdeal.num_eq_zero_iff]

private theorem coe_conjInvariantIntegralRep
    (K : Type*) [Field K] [NumberField K] [Algebra ℚ K]
    [QuadraticField K] [QuadraticField.Conj K]
    (F : FractionalIdeal (NumberField.RingOfIntegers K)⁰
      (FractionRing (NumberField.RingOfIntegers K))) :
    ((conjInvariantIntegralRep K F : Ideal (NumberField.RingOfIntegers K)) :
        FractionalIdeal (NumberField.RingOfIntegers K)⁰
          (FractionRing (NumberField.RingOfIntegers K))) =
      FractionalIdeal.spanSingleton (NumberField.RingOfIntegers K)⁰
          (algebraMap (NumberField.RingOfIntegers K)
            (FractionRing (NumberField.RingOfIntegers K))
            (((F.den : NumberField.RingOfIntegers K) *
              conjAutRingOfIntegers K (F.den : NumberField.RingOfIntegers K)) ^ 2)) *
        F := by
  let R := NumberField.RingOfIntegers K
  let a : R := F.den
  let b : R := conjAutRingOfIntegers K a
  change ((Ideal.span ({a * b ^ 2} : Set R) * F.num : Ideal R) :
      FractionalIdeal R⁰ (FractionRing R)) =
    FractionalIdeal.spanSingleton R⁰
        (algebraMap R (FractionRing R) ((a * b) ^ 2)) * F
  calc
    ((Ideal.span ({a * b ^ 2} : Set R) * F.num : Ideal R) :
        FractionalIdeal R⁰ (FractionRing R)) =
        (Ideal.span ({a * b ^ 2} : Set R) : FractionalIdeal R⁰ (FractionRing R)) *
          (F.num : FractionalIdeal R⁰ (FractionRing R)) := by
      rw [FractionalIdeal.coeIdeal_mul]
    _ =
        FractionalIdeal.spanSingleton R⁰
            (algebraMap R (FractionRing R) (a * b ^ 2)) *
          (F.num : FractionalIdeal R⁰ (FractionRing R)) := by
      rw [FractionalIdeal.coeIdeal_span_singleton]
    _ =
        FractionalIdeal.spanSingleton R⁰
            (algebraMap R (FractionRing R) (a * b ^ 2)) *
          (FractionalIdeal.spanSingleton R⁰ (algebraMap R (FractionRing R) a) * F) := by
      rw [FractionalIdeal.den_mul_self_eq_num']
    _ =
        FractionalIdeal.spanSingleton R⁰
            (algebraMap R (FractionRing R) ((a * b) ^ 2)) * F := by
      rw [← mul_assoc, FractionalIdeal.spanSingleton_mul_spanSingleton]
      congr 1
      simp [pow_two, mul_left_comm, mul_comm]

private theorem conjAutRingOfIntegers_mul_conj_fixed
    (K : Type*) [Field K] [Algebra ℚ K]
    [QuadraticField K] [QuadraticField.Conj K]
    (a : NumberField.RingOfIntegers K) :
    conjAutRingOfIntegers K (a * conjAutRingOfIntegers K a) =
      a * conjAutRingOfIntegers K a := by
  rw [map_mul, conjAutRingOfIntegers_apply_apply, mul_comm]

private theorem conjInvariantIntegralRep_isAmbiguous
    (K : Type*) [Field K] [NumberField K] [Algebra ℚ K]
    [QuadraticField K] [QuadraticField.Conj K]
    (F : (FractionalIdeal (NumberField.RingOfIntegers K)⁰
      (FractionRing (NumberField.RingOfIntegers K)))ˣ)
    (hFfixed :
      FractionalIdeal.ringEquivMap
          (K := FractionRing (NumberField.RingOfIntegers K))
          (L := FractionRing (NumberField.RingOfIntegers K))
          (conjAutRingOfIntegers K) F.1 = F.1) :
    IsAmbiguousIdeal (conjAutRingOfIntegers K)
      (conjInvariantIntegralRep K F.1) := by
  let R := NumberField.RingOfIntegers K
  let σ := conjAutRingOfIntegers K
  let c : R := (F.1.den : R) * σ (F.1.den : R)
  have hc : σ c = c := by
    dsimp [c, σ]
    exact conjAutRingOfIntegers_mul_conj_fixed K (F.1.den : R)
  have hzc :
      IsFractionRing.ringEquivOfRingEquiv
          (K := FractionRing R) (L := FractionRing R) σ
          (algebraMap R (FractionRing R) (c ^ 2)) =
        algebraMap R (FractionRing R) (c ^ 2) := by
    rw [IsFractionRing.ringEquivOfRingEquiv_algebraMap, map_pow, hc]
  have hmap :
      FractionalIdeal.ringEquivMap
          (K := FractionRing R) (L := FractionRing R) σ
          ((conjInvariantIntegralRep K F.1 : Ideal R) :
            FractionalIdeal R⁰ (FractionRing R)) =
        ((conjInvariantIntegralRep K F.1 : Ideal R) :
          FractionalIdeal R⁰ (FractionRing R)) := by
    rw [coe_conjInvariantIntegralRep, FractionalIdeal.ringEquivMap_mul,
      FractionalIdeal.ringEquivMap_spanSingleton, hFfixed, hzc]
  have hmapIdeal :
      ((Ideal.map (σ : R →+* R) (conjInvariantIntegralRep K F.1) : Ideal R) :
        FractionalIdeal R⁰ (FractionRing R)) =
      ((conjInvariantIntegralRep K F.1 : Ideal R) :
        FractionalIdeal R⁰ (FractionRing R)) := by
    simpa [σ, FractionalIdeal.ringEquivMap_coeIdeal] using hmap
  exact (FractionalIdeal.coeIdeal_inj (K := FractionRing R)).mp hmapIdeal

private theorem exists_tp_multiplier_conjInvariantIntegralRep
    (K : Type*) [Field K] [NumberField K] [Algebra ℚ K]
    [QuadraticField K] [QuadraticField.Conj K]
    (F : (FractionalIdeal (NumberField.RingOfIntegers K)⁰
      (FractionRing (NumberField.RingOfIntegers K)))ˣ) :
    ∃ t : (FractionRing (NumberField.RingOfIntegers K))ˣ,
      NarrowClassGroup.IsTotallyPositive
        (t : FractionRing (NumberField.RingOfIntegers K)) ∧
        FractionalIdeal.mk0 (FractionRing (NumberField.RingOfIntegers K))
            ⟨conjInvariantIntegralRep K F.1,
              conjInvariantIntegralRep_mem_nonZeroDivisors K F.ne_zero⟩ *
          toPrincipalIdeal (NumberField.RingOfIntegers K)
            (FractionRing (NumberField.RingOfIntegers K)) t =
        F := by
  let R := NumberField.RingOfIntegers K
  let a : R := F.1.den
  let b : R := conjAutRingOfIntegers K a
  let c : R := a * b
  let z : FractionRing R := algebraMap R (FractionRing R) c
  have ha0 : a ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp F.1.den.prop
  have hb0 : b ≠ 0 := by
    dsimp [b]
    intro hb
    exact ha0 ((conjAutRingOfIntegers K).injective (by simpa using hb))
  have hc0 : c ≠ 0 := mul_ne_zero ha0 hb0
  have hz0 : z ≠ 0 :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors
      (mem_nonZeroDivisors_iff_ne_zero.mpr hc0)
  let t : (FractionRing R)ˣ := Units.mk0 (z⁻¹ ^ 2) (pow_ne_zero 2 (inv_ne_zero hz0))
  refine ⟨t, ?_, ?_⟩
  · exact NarrowClassGroup.isTotallyPositive_sq_of_ne_zero z⁻¹ (inv_ne_zero hz0)
  · apply Units.ext
    change
      ((conjInvariantIntegralRep K F.1 : Ideal R) : FractionalIdeal R⁰ (FractionRing R)) *
          (toPrincipalIdeal R (FractionRing R) t :
            FractionalIdeal R⁰ (FractionRing R)) =
        F.1
    rw [coe_conjInvariantIntegralRep, coe_toPrincipalIdeal]
    have hzsq :
        algebraMap R (FractionRing R)
            (((F.1.den : R) *
              conjAutRingOfIntegers K (F.1.den : R)) ^ 2) =
          z ^ 2 := by
      simp [z, c, a, b, map_pow]
    have ht : (t : FractionRing R) = z⁻¹ ^ 2 := rfl
    rw [hzsq, ht]
    calc
      (FractionalIdeal.spanSingleton R⁰ (z ^ 2) * F.1) *
          FractionalIdeal.spanSingleton R⁰ (z⁻¹ ^ 2) =
          F.1 *
            (FractionalIdeal.spanSingleton R⁰ (z ^ 2) *
              FractionalIdeal.spanSingleton R⁰ (z⁻¹ ^ 2)) := by
        ac_rfl
      _ = F.1 * FractionalIdeal.spanSingleton R⁰ 1 := by
        have hzinv : z ^ 2 * (z⁻¹ ^ 2) = 1 := by
          rw [← mul_pow, mul_inv_cancel₀ hz0, one_pow]
        rw [FractionalIdeal.spanSingleton_mul_spanSingleton, hzinv]
      _ = F.1 := by
        rw [FractionalIdeal.spanSingleton_one, mul_one]

/-- Integral clearing boundary for a conjugation-stable fractional representative.
If the fractional representative `I * (y)` matches its conjugate factorization,
then an ambiguous integral ideal represents the same narrow class, up to a
totally positive principal multiplier. -/
private theorem exists_ambiguousIntegralClearing_of_conjAutFractionalRep_eq
    (K : Type*) [Field K] [NumberField K] [Algebra ℚ K]
    [QuadraticField K] [QuadraticField.Conj K]
    (I : (Ideal (NumberField.RingOfIntegers K))⁰)
    (y : (FractionRing (NumberField.RingOfIntegers K))ˣ)
    (hfixed :
      FractionalIdeal.mk0 (FractionRing (NumberField.RingOfIntegers K)) I *
          toPrincipalIdeal (NumberField.RingOfIntegers K)
            (FractionRing (NumberField.RingOfIntegers K)) y =
        FractionalIdeal.mk0 (FractionRing (NumberField.RingOfIntegers K))
            (conjAutNonzeroIdealMulEquiv K I) *
          toPrincipalIdeal (NumberField.RingOfIntegers K)
            (FractionRing (NumberField.RingOfIntegers K))
            (Units.mapEquiv (conjAutFractionRingAlgEquiv K).toRingEquiv y)) :
    ∃ J : (Ideal (NumberField.RingOfIntegers K))⁰,
      IsAmbiguousIdeal (conjAutRingOfIntegers K)
          (J : Ideal (NumberField.RingOfIntegers K)) ∧
        ∃ t : (FractionRing (NumberField.RingOfIntegers K))ˣ,
          NarrowClassGroup.IsTotallyPositive
            (t : FractionRing (NumberField.RingOfIntegers K)) ∧
            FractionalIdeal.mk0 (FractionRing (NumberField.RingOfIntegers K)) J *
                toPrincipalIdeal (NumberField.RingOfIntegers K)
                  (FractionRing (NumberField.RingOfIntegers K)) t =
              FractionalIdeal.mk0 (FractionRing (NumberField.RingOfIntegers K)) I *
                toPrincipalIdeal (NumberField.RingOfIntegers K)
                  (FractionRing (NumberField.RingOfIntegers K)) y := by
  let R := NumberField.RingOfIntegers K
  let F : (FractionalIdeal R⁰ (FractionRing R))ˣ :=
    FractionalIdeal.mk0 (FractionRing R) I *
      toPrincipalIdeal R (FractionRing R) y
  have hFfixed :
      FractionalIdeal.ringEquivMap
          (K := FractionRing R) (L := FractionRing R)
          (conjAutRingOfIntegers K) F.1 = F.1 := by
    simpa [F, R] using
      ringEquivMap_conjAut_fractionalRep_eq_self_of_eq_conjAutFractionalRep
        K I y hfixed
  let J : (Ideal R)⁰ :=
    ⟨conjInvariantIntegralRep K F.1,
      conjInvariantIntegralRep_mem_nonZeroDivisors K F.ne_zero⟩
  obtain ⟨t, htpos, ht⟩ := exists_tp_multiplier_conjInvariantIntegralRep K F
  refine ⟨J, ?_, t, htpos, ?_⟩
  · simpa [J, R] using conjInvariantIntegralRep_isAmbiguous K F hFfixed
  · simpa [J, F, R] using ht

/-- Integral clearing boundary for a conjugation-stable fractional representative.
If the fractional representative `I * (y)` matches its conjugate factorization,
then it has an ambiguous integral ideal representative in the same narrow
class. -/
private theorem exists_integralIdeal_ambiguous_fractionalRep_of_conjAutFractionalRep_eq
    (K : Type*) [Field K] [NumberField K] [Algebra ℚ K]
    [QuadraticField K] [QuadraticField.Conj K]
    (I : (Ideal (NumberField.RingOfIntegers K))⁰)
    (y : (FractionRing (NumberField.RingOfIntegers K))ˣ)
    (hfixed :
      FractionalIdeal.mk0 (FractionRing (NumberField.RingOfIntegers K)) I *
          toPrincipalIdeal (NumberField.RingOfIntegers K)
            (FractionRing (NumberField.RingOfIntegers K)) y =
        FractionalIdeal.mk0 (FractionRing (NumberField.RingOfIntegers K))
            (conjAutNonzeroIdealMulEquiv K I) *
          toPrincipalIdeal (NumberField.RingOfIntegers K)
            (FractionRing (NumberField.RingOfIntegers K))
            (Units.mapEquiv (conjAutFractionRingAlgEquiv K).toRingEquiv y)) :
    ∃ J : (Ideal (NumberField.RingOfIntegers K))⁰,
      NarrowClassGroup.mk0 J =
        NarrowClassGroup.mk
          (FractionalIdeal.mk0 (FractionRing (NumberField.RingOfIntegers K)) I *
            toPrincipalIdeal (NumberField.RingOfIntegers K)
              (FractionRing (NumberField.RingOfIntegers K)) y) ∧
        IsAmbiguousIdeal (conjAutRingOfIntegers K)
          (J : Ideal (NumberField.RingOfIntegers K)) := by
  obtain ⟨J, hJamb, t, htpos, ht⟩ :=
    exists_ambiguousIntegralClearing_of_conjAutFractionalRep_eq K I y hfixed
  refine ⟨J, ?_, hJamb⟩
  rw [← NarrowClassGroup.mk_mk0]
  exact NarrowClassGroup.mk_eq_mk.mpr ⟨⟨t, htpos⟩, ht⟩

/-- Integral clearing boundary for a coboundary-adjusted fractional ideal. Under
the coboundary relation, the fractional ideal `I * (y)` should have an ambiguous
integral representative in the same narrow class. -/
private theorem exists_integralIdeal_ambiguous_fractionalRep_of_conjAut_coboundary
    (K : Type*) [Field K] [NumberField K] [Algebra ℚ K]
    [QuadraticField K] [QuadraticField.Conj K]
    (I : (Ideal (NumberField.RingOfIntegers K))⁰)
    {x y : (FractionRing (NumberField.RingOfIntegers K))ˣ}
    (hy :
      x = y * (Units.mapEquiv (conjAutFractionRingAlgEquiv K).toRingEquiv y)⁻¹)
    (hconj :
      FractionalIdeal.mk0 (FractionRing (NumberField.RingOfIntegers K)) I *
          toPrincipalIdeal (NumberField.RingOfIntegers K)
            (FractionRing (NumberField.RingOfIntegers K)) x =
        FractionalIdeal.mk0 (FractionRing (NumberField.RingOfIntegers K))
          (conjAutNonzeroIdealMulEquiv K I)) :
    ∃ J : (Ideal (NumberField.RingOfIntegers K))⁰,
      NarrowClassGroup.mk0 J =
        NarrowClassGroup.mk
          (FractionalIdeal.mk0 (FractionRing (NumberField.RingOfIntegers K)) I *
            toPrincipalIdeal (NumberField.RingOfIntegers K)
              (FractionRing (NumberField.RingOfIntegers K)) y) ∧
        IsAmbiguousIdeal (conjAutRingOfIntegers K)
          (J : Ideal (NumberField.RingOfIntegers K)) := by
  exact
    exists_integralIdeal_ambiguous_fractionalRep_of_conjAutFractionalRep_eq
      K I y (fractionalRep_eq_conjAutFractionalRep_of_coboundary K I hy hconj)

/-- Coboundary-to-ideal boundary. If the conjugation multiplier is a totally
positive coboundary, multiplying by the coboundary gives an ambiguous integral
ideal representative in the same narrow class. -/
private theorem exists_integralIdeal_isAmbiguousIdeal_mk0_eq_of_conjAut_coboundary
    (K : Type*) [Field K] [NumberField K] [Algebra ℚ K]
    [QuadraticField K] [QuadraticField.Conj K]
    (I : (Ideal (NumberField.RingOfIntegers K))⁰)
    {x y : (FractionRing (NumberField.RingOfIntegers K))ˣ}
    (hypos : NarrowClassGroup.IsTotallyPositive
      (y : FractionRing (NumberField.RingOfIntegers K)))
    (hy :
      x = y * (Units.mapEquiv (conjAutFractionRingAlgEquiv K).toRingEquiv y)⁻¹)
    (hconj :
      FractionalIdeal.mk0 (FractionRing (NumberField.RingOfIntegers K)) I *
          toPrincipalIdeal (NumberField.RingOfIntegers K)
            (FractionRing (NumberField.RingOfIntegers K)) x =
        FractionalIdeal.mk0 (FractionRing (NumberField.RingOfIntegers K))
          (conjAutNonzeroIdealMulEquiv K I)) :
    ∃ J : (Ideal (NumberField.RingOfIntegers K))⁰,
      NarrowClassGroup.mk0 J = NarrowClassGroup.mk0 I ∧
        IsAmbiguousIdeal (conjAutRingOfIntegers K)
          (J : Ideal (NumberField.RingOfIntegers K)) := by
  obtain ⟨J, hJmk, hJamb⟩ :=
    exists_integralIdeal_ambiguous_fractionalRep_of_conjAut_coboundary
      K I hy hconj
  refine ⟨J, ?_, hJamb⟩
  have hmk :
      NarrowClassGroup.mk (FractionalIdeal.mk0 (FractionRing (NumberField.RingOfIntegers K)) I) =
        NarrowClassGroup.mk
          (FractionalIdeal.mk0 (FractionRing (NumberField.RingOfIntegers K)) I *
            toPrincipalIdeal (NumberField.RingOfIntegers K)
              (FractionRing (NumberField.RingOfIntegers K)) y) := by
    refine NarrowClassGroup.mk_eq_mk.mpr ?_
    exact ⟨⟨y, hypos⟩, rfl⟩
  exact hJmk.trans hmk.symm

/-- Hilbert-90 adjustment boundary. A representative whose conjugate differs by
a totally positive principal fractional ideal can be changed within the same
narrow class to a genuinely ambiguous integral ideal. -/
private theorem exists_integralIdeal_isAmbiguousIdeal_mk0_eq_of_tp_multiplier_to_conjAut
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)]
    (I : (Ideal (NumberField.RingOfIntegers (Qsqrtd (d : ℚ))))⁰)
    {x : (FractionRing (NumberField.RingOfIntegers (Qsqrtd (d : ℚ))))ˣ}
    (hxpos : NarrowClassGroup.IsTotallyPositive
      (x : FractionRing (NumberField.RingOfIntegers (Qsqrtd (d : ℚ)))))
    (hconj :
      FractionalIdeal.mk0
          (FractionRing (NumberField.RingOfIntegers (Qsqrtd (d : ℚ)))) I *
        toPrincipalIdeal (NumberField.RingOfIntegers (Qsqrtd (d : ℚ)))
          (FractionRing (NumberField.RingOfIntegers (Qsqrtd (d : ℚ)))) x =
      FractionalIdeal.mk0
        (FractionRing (NumberField.RingOfIntegers (Qsqrtd (d : ℚ))))
        (conjAutNonzeroIdealMulEquiv (Qsqrtd (d : ℚ)) I)) :
    ∃ J : (Ideal (NumberField.RingOfIntegers (Qsqrtd (d : ℚ))))⁰,
      NarrowClassGroup.mk0 J = NarrowClassGroup.mk0 I ∧
        IsAmbiguousIdeal (conjAutRingOfIntegers (Qsqrtd (d : ℚ)))
          (J : Ideal (NumberField.RingOfIntegers (Qsqrtd (d : ℚ)))) := by
  obtain ⟨y, hypos, hy⟩ :=
    exists_totallyPositive_conjAut_coboundary_of_tp_multiplier_to_conjAut
      d I hxpos hconj
  exact exists_integralIdeal_isAmbiguousIdeal_mk0_eq_of_conjAut_coboundary
    (Qsqrtd (d : ℚ)) I hypos hy hconj

/-- Per-factor assembly boundary in principal-multiplier form. A genuinely
ambiguous integral ideal differs from the product of its ramified-prime parity
factors by a totally positive principal fractional ideal. -/
private theorem exists_tp_multiplier_ambiguousIdeal_to_fullRamifiedParityIdealProduct
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
  -- Remaining gap: multiply the explicit positive base-prime span contributions
  -- supplied by `factor_contribution_by_splitting_span` over the Dedekind
  -- factorization of `J`. Split conjugate pairs and inert prime factors cancel
  -- as totally positive principal ideals, while ramified factors reduce to their
  -- exponent modulo `2`.
  sorry

/-- Per-factor assembly boundary in class form. A genuinely ambiguous integral
ideal class is the class of the full ramified-prime parity product. -/
private theorem ambiguousIdeal_mk0_eq_fullRamifiedParityIdealProduct
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)]
    (J : (Ideal (NumberField.RingOfIntegers (Qsqrtd (d : ℚ))))⁰)
    (hJ : IsAmbiguousIdeal (conjAutRingOfIntegers (Qsqrtd (d : ℚ)))
      (J : Ideal (NumberField.RingOfIntegers (Qsqrtd (d : ℚ))))) :
    NarrowClassGroup.mk0 J =
      NarrowClassGroup.mk0
        (fullRamifiedParityIdealProduct d (fullRamifiedParityVector d J)) := by
  rw [NarrowClassGroup.mk0_eq_mk0_iff_exists_fraction_ring]
  exact exists_tp_multiplier_ambiguousIdeal_to_fullRamifiedParityIdealProduct d J hJ

/-- If the distinguished coordinate is zero, the full ramified parity ideal
product is literally the erased ramified parity ideal product obtained by
restricting the vector away from that coordinate. -/
private theorem fullRamifiedParityIdealProduct_eq_ramifiedParityIdealProduct_of_apply_p0_eq_zero
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
private theorem fullRamifiedParityNarrowClassProduct_eq_erased_of_apply_p0_eq_zero
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

/-- Positive-principal denominator boundary in narrow-class form. For the full
ramified parity vector actually attached to an ambiguous ideal, the distinguished
ramified coordinate can be removed in `Cl⁺`. This is deliberately not stated for
an arbitrary full vector: in real quadratic fields the naive total finite
ramified-prime product is not generally narrow-principal. -/
private theorem exists_erasedRamifiedParityProduct_mk0_eq_full_of_ambiguousIdeal
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)]
    {p0 : ℕ} (hp0 : p0 ∈ ramifiedPrimes d)
    (J : (Ideal (NumberField.RingOfIntegers (Qsqrtd (d : ℚ))))⁰)
    (hJ : IsAmbiguousIdeal (conjAutRingOfIntegers (Qsqrtd (d : ℚ)))
      (J : Ideal (NumberField.RingOfIntegers (Qsqrtd (d : ℚ))))) :
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
  · let u : {p // p ∈ ramifiedPrimes d} → Fin 2 := fun p => if v p = 0 then 1 else 0
    refine ⟨fun p => u ⟨p.1, (Finset.mem_erase.mp p.2).2⟩, ?_⟩
    -- Remaining gap: use the strict/narrow ambiguous class number denominator
    -- for the actual ambiguous ideal `J`. The older arbitrary-vector statement
    -- was too strong: the finite total ramified product need not be
    -- narrow-principal in real quadratic fields.
    sorry

/-- The full ramified parity ideal product is the multiset product of exactly the
ramified prime ideals whose parity coordinate is nonzero. -/
private theorem coe_fullRamifiedParityIdealProduct_eq_filtered_multiset_prod
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
private theorem normalizedFactors_count_fullRamifiedParityIdealProduct
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
private theorem fullRamifiedParityVector_fullRamifiedParityIdealProduct
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)]
    (v : ({p // p ∈ ramifiedPrimes d} → Fin 2)) :
    fullRamifiedParityVector d (fullRamifiedParityIdealProduct d v) = v := by
  funext p
  apply Fin.ext
  dsimp [fullRamifiedParityVector]
  rw [normalizedFactors_count_fullRamifiedParityIdealProduct d v p]
  exact Nat.mod_eq_of_lt (v p).isLt

/-- The erased ramified parity ideal product is the multiset product of exactly
the ramified prime ideals whose parity coordinate is nonzero. -/
private theorem coe_ramifiedParityIdealProduct_eq_filtered_multiset_prod
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
private theorem normalizedFactors_count_ramifiedParityIdealProduct
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
private theorem idealRamifiedParityVector_ramifiedParityIdealProduct
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
private theorem exists_integralIdeal_erasedRamifiedParityRepresentative_of_isAmbiguousIdeal
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)]
    {p0 : ℕ} (hp0 : p0 ∈ ramifiedPrimes d)
    (J : (Ideal (NumberField.RingOfIntegers (Qsqrtd (d : ℚ))))⁰)
    (hJ : IsAmbiguousIdeal (conjAutRingOfIntegers (Qsqrtd (d : ℚ)))
      (J : Ideal (NumberField.RingOfIntegers (Qsqrtd (d : ℚ))))) :
    ∃ I : (Ideal (NumberField.RingOfIntegers (Qsqrtd (d : ℚ))))⁰,
      NarrowClassGroup.mk0 I = NarrowClassGroup.mk0 J ∧
        NarrowClassGroup.mk0 I =
          NarrowClassGroup.mk0
            (ramifiedParityIdealProduct d hp0 (idealRamifiedParityVector d hp0 I)) := by
  obtain ⟨w, hw⟩ :=
    exists_erasedRamifiedParityProduct_mk0_eq_full_of_ambiguousIdeal
      d hp0 J hJ
  let I := ramifiedParityIdealProduct d hp0 w
  refine ⟨I, ?_, ?_⟩
  · exact hw.trans (ambiguousIdeal_mk0_eq_fullRamifiedParityIdealProduct d J hJ).symm
  · simp [I, idealRamifiedParityVector_ramifiedParityIdealProduct d hp0 w]

/-- Hard representative selection for the ambiguous bound. It chooses a
representative of an inversion-fixed narrow class whose ramified-prime parity
vector actually represents the same narrow class. Proving this is the remaining
mathematical boundary: use the fixed-class Hilbert-90 adjustment, cancel
split/inert/non-ramified prime-ideal orbits, and apply the single product-one
relation among ramified primes. -/
private theorem exists_integralIdeal_ramifiedParityRepresentative_of_narrowInversionFixedClass
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)]
    {p0 : ℕ} (hp0 : p0 ∈ ramifiedPrimes d)
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
      d hp0 J hJamb
  refine ⟨J', ?_, hJ'parity⟩
  exact hJ'mk0.trans (hJmk0.trans hI)

private noncomputable def narrowInversionFixedRepresentativeIdeal
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)]
    {p0 : ℕ} (hp0 : p0 ∈ ramifiedPrimes d)
    (C : NarrowInversionFixedClass (NumberField.RingOfIntegers (Qsqrtd (d : ℚ)))) :
    (Ideal (NumberField.RingOfIntegers (Qsqrtd (d : ℚ))))⁰ :=
  Classical.choose
    (exists_integralIdeal_ramifiedParityRepresentative_of_narrowInversionFixedClass
      d hp0 C)

private theorem narrowInversionFixedRepresentativeIdeal_mk0
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)]
    {p0 : ℕ} (hp0 : p0 ∈ ramifiedPrimes d)
    (C : NarrowInversionFixedClass (NumberField.RingOfIntegers (Qsqrtd (d : ℚ)))) :
    NarrowClassGroup.mk0 (narrowInversionFixedRepresentativeIdeal d hp0 C) = C.1 :=
  (Classical.choose_spec
    (exists_integralIdeal_ramifiedParityRepresentative_of_narrowInversionFixedClass
      d hp0 C)).1

private theorem narrowInversionFixedRepresentativeIdeal_mk0_eq_ramifiedParityIdealProduct
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)]
    {p0 : ℕ} (hp0 : p0 ∈ ramifiedPrimes d)
    (C : NarrowInversionFixedClass (NumberField.RingOfIntegers (Qsqrtd (d : ℚ)))) :
    NarrowClassGroup.mk0 (narrowInversionFixedRepresentativeIdeal d hp0 C) =
      NarrowClassGroup.mk0
        (ramifiedParityIdealProduct d hp0
          (idealRamifiedParityVector d hp0
            (narrowInversionFixedRepresentativeIdeal d hp0 C))) :=
  (Classical.choose_spec
    (exists_integralIdeal_ramifiedParityRepresentative_of_narrowInversionFixedClass
      d hp0 C)).2

private noncomputable def narrowInversionFixedClassRamifiedParityVector
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)]
    {p0 : ℕ} (hp0 : p0 ∈ ramifiedPrimes d) :
    NarrowInversionFixedClass (NumberField.RingOfIntegers (Qsqrtd (d : ℚ))) →
      ({p // p ∈ (ramifiedPrimes d).erase p0} → Fin 2) := by
  classical
  intro C
  exact idealRamifiedParityVector d hp0
    (narrowInversionFixedRepresentativeIdeal d hp0 C)

/-- Exact remaining fixed-representative recovery input for the ambiguous-ideal
bound. It says that the chosen representative of an inversion-fixed narrow
class differs from the ramified parity ideal product by a totally positive
principal fractional ideal. This is the point where the proof still needs the
fixed-ideal representative/factorization theorem and the product-one
positive-principal relation for ramified primes. -/
private theorem exists_tp_multiplier_representative_to_ramifiedParityIdealProduct
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)]
    {p0 : ℕ} (hp0 : p0 ∈ ramifiedPrimes d)
    (C : NarrowInversionFixedClass (NumberField.RingOfIntegers (Qsqrtd (d : ℚ)))) :
    ∃ x : (FractionRing (NumberField.RingOfIntegers (Qsqrtd (d : ℚ))))ˣ,
      NarrowClassGroup.IsTotallyPositive
        (x : FractionRing (NumberField.RingOfIntegers (Qsqrtd (d : ℚ)))) ∧
        FractionalIdeal.mk0
            (FractionRing (NumberField.RingOfIntegers (Qsqrtd (d : ℚ))))
            (narrowInversionFixedRepresentativeIdeal d hp0 C) *
          toPrincipalIdeal (NumberField.RingOfIntegers (Qsqrtd (d : ℚ)))
            (FractionRing (NumberField.RingOfIntegers (Qsqrtd (d : ℚ)))) x =
        FractionalIdeal.mk0
          (FractionRing (NumberField.RingOfIntegers (Qsqrtd (d : ℚ))))
          (ramifiedParityIdealProduct d hp0
            (narrowInversionFixedClassRamifiedParityVector d hp0 C)) := by
  have hclass :
      NarrowClassGroup.mk0 (narrowInversionFixedRepresentativeIdeal d hp0 C) =
        NarrowClassGroup.mk0
          (ramifiedParityIdealProduct d hp0
            (narrowInversionFixedClassRamifiedParityVector d hp0 C)) := by
    simpa [narrowInversionFixedClassRamifiedParityVector] using
      narrowInversionFixedRepresentativeIdeal_mk0_eq_ramifiedParityIdealProduct
        d hp0 C
  exact (NarrowClassGroup.mk0_eq_mk0_iff_exists_fraction_ring).mp hclass

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
  obtain ⟨p0, hp0⟩ : (ramifiedPrimes d).Nonempty := by
    rw [← Finset.card_pos, ← ramifiedPrimeCount_eq_card]
    exact Nat.lt_of_lt_of_le Nat.zero_lt_one (one_le_ramifiedPrimeCount d)
  let ramifiedParityVector := narrowInversionFixedClassRamifiedParityVector d hp0
  have hrecoverByRamifiedParity :
      ∀ C : NarrowInversionFixedClass R,
        C.1 = ramifiedParityNarrowClassProduct d hp0 (ramifiedParityVector C) := by
    intro C
    let I := narrowInversionFixedRepresentativeIdeal d hp0 C
    let J := ramifiedParityIdealProduct d hp0 (ramifiedParityVector C)
    have hI_mk0 : NarrowClassGroup.mk0 I = C.1 :=
      narrowInversionFixedRepresentativeIdeal_mk0 d hp0 C
    have hJ_mk0 :
        NarrowClassGroup.mk0 J =
          ramifiedParityNarrowClassProduct d hp0 (ramifiedParityVector C) := by
      simpa [J] using mk0_ramifiedParityIdealProduct d hp0 (ramifiedParityVector C)
    rw [← hI_mk0]
    rw [← hJ_mk0]
    rw [NarrowClassGroup.mk0_eq_mk0_iff_exists_fraction_ring]
    -- This named boundary supplies the multiplier from the chosen fixed-class
    -- representative to the ramified parity ideal product.
    simpa only [I, J, ramifiedParityVector] using
      exists_tp_multiplier_representative_to_ramifiedParityIdealProduct d hp0 C
  have hramifiedParityVector_injective : Function.Injective ramifiedParityVector := by
    intro C D hCD
    apply Subtype.ext
    rw [hrecoverByRamifiedParity C, hrecoverByRamifiedParity D, hCD]
  exact card_le_genusBound_of_injective_to_ramifiedParityVectors (d := d) hp0
    ramifiedParityVector hramifiedParityVector_injective

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
