/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/

import Mathlib.RepresentationTheory.Homological.GroupCohomology.Hilbert90
import Mathlib.RingTheory.Invariant.Basic
import QNFMathlib.NumberTheory.NumberField.Galois
import QuadraticNumberFields.QuadraticField.Conj
import QuadraticNumberFields.QuadraticField.Galois
import QuadraticNumberFields.QuadraticField.RingOfIntegers
import QuadraticNumberFields.RingOfIntegers.Norm

/-!
# Quadratic Conjugation on the Ring of Integers

This file develops quadratic conjugation on the ring of integers `𝓞 K` of a
quadratic number field `K`: its `ℤ`-algebra and fraction-field avatars, the
induced Galois element of `FractionRing 𝓞 K / FractionRing ℤ`, the Hilbert 90
specialization, and involutivity. These are the ring-level conjugation
primitives consumed by the ambiguous-class layer.
-/

namespace QuadraticNumberFields

open scoped nonZeroDivisors NumberField Pointwise

attribute [-instance] DivisionRing.toRatAlgebra
attribute [local instance] FractionRing.liftAlgebra

section RingOfIntegersConjugation

variable (K : Type*) [Field K] [Algebra ℚ K] [QuadraticField K] [QuadraticField.Conj K]

local notation "OK" => NumberField.RingOfIntegers K

noncomputable local instance instMulSemiringActionFractionRingGalRingOfIntegersConj
    [NumberField K] :
    MulSemiringAction Gal(FractionRing OK / FractionRing ℤ) OK :=
  IsIntegralClosure.MulSemiringAction ℤ (FractionRing ℤ) (FractionRing OK) OK

/-! ## Ring-of-integers conjugation -/

/-- The conjugation of a quadratic field `K`, restricted to its ring of integers.
This is the automorphism whose fixed ideals are the ambiguous ideals. -/
noncomputable def conjAutRingOfIntegers : OK ≃+* OK :=
  NumberField.RingOfIntegers.mapRingEquiv (QuadraticField.conjAut K).toRingEquiv

/-- Coercing ring-of-integers conjugation to `K` agrees with field conjugation. -/
@[simp]
theorem coe_conjAutRingOfIntegers_apply (x : OK) :
    (conjAutRingOfIntegers K x : K) = QuadraticField.conjAut K x := by
  rw [conjAutRingOfIntegers, NumberField.RingOfIntegers.mapRingEquiv_apply]
  rfl

/-- The conjugation of the ring of integers, regarded as a `ℤ`-algebra
automorphism. -/
noncomputable def conjAutRingOfIntegersAlgEquiv : OK ≃ₐ[ℤ] OK :=
  AlgEquiv.ofRingEquiv (f := conjAutRingOfIntegers K) (by
    intro n
    ext
    rw [coe_conjAutRingOfIntegers_apply]
    simp)

/-- Coercing the `ℤ`-algebra version of ring-of-integers conjugation to `K`
agrees with field conjugation. -/
theorem coe_conjAutRingOfIntegersAlgEquiv_apply (x : OK) :
    (conjAutRingOfIntegersAlgEquiv K x : K) = QuadraticField.conjAut K x := by
  rw [conjAutRingOfIntegersAlgEquiv]
  exact coe_conjAutRingOfIntegers_apply K x

/-- Restricting field conjugation to the ring of integers gives the
`ℤ`-algebra automorphism `conjAutRingOfIntegersAlgEquiv`. -/
theorem galRestrict_conjAut_eq_conjAutRingOfIntegers [NumberField K] :
    galRestrict ℤ ℚ K OK (QuadraticField.conjAut K) =
      conjAutRingOfIntegersAlgEquiv K := by
  ext x
  simpa [conjAutRingOfIntegersAlgEquiv, coe_conjAutRingOfIntegers_apply] using
    (algebraMap_galRestrict_apply (A := ℤ) (QuadraticField.conjAut K) x)

/-- The induced `ℤ`-algebra conjugation on the ring of integers is nontrivial. -/
theorem conjAutRingOfIntegersAlgEquiv_ne_refl [NumberField K] :
    conjAutRingOfIntegersAlgEquiv K ≠ AlgEquiv.refl := by
  intro h
  apply QuadraticField.Conj.conj_ne_refl (K := K)
  exact (galRestrict ℤ ℚ K OK).injective <| by
    rw [galRestrict_conjAut_eq_conjAutRingOfIntegers K, h]
    exact (map_one (galRestrict ℤ ℚ K OK)).symm

/-- Quadratic conjugation on the fraction field of the ring of integers, obtained
by localizing the ring-of-integers conjugation. -/
noncomputable def conjAutFractionRingAlgEquiv [NumberField K] :
    FractionRing OK ≃ₐ[ℤ] FractionRing OK :=
  IsFractionRing.algEquivOfAlgEquiv (conjAutRingOfIntegersAlgEquiv K)

/-- Fraction-field conjugation sends an embedded algebraic integer to the
embedded conjugate algebraic integer. -/
@[simp]
theorem conjAutFractionRingAlgEquiv_algebraMap [NumberField K] (x : OK) :
    conjAutFractionRingAlgEquiv K
        (algebraMap OK (FractionRing OK) x) =
      algebraMap OK (FractionRing OK) ((conjAutRingOfIntegers K) x) := by
  simp [conjAutFractionRingAlgEquiv, conjAutRingOfIntegersAlgEquiv]

/-- Transporting fraction-field conjugation to `K` agrees with quadratic field
conjugation on `K`. -/
@[simp]
theorem fractionRing_algEquiv_conjAutFractionRingAlgEquiv [NumberField K]
    (z : FractionRing OK) :
    FractionRing.algEquiv OK K
        ((conjAutFractionRingAlgEquiv K) z) =
      QuadraticField.conjAut K
        (FractionRing.algEquiv OK K z) := by
  let R := OK
  have hhom :
      ((FractionRing.algEquiv R K).toRingHom.comp
          (conjAutFractionRingAlgEquiv K).toRingHom) =
        ((QuadraticField.conjAut K).toRingHom.comp
          (FractionRing.algEquiv R K).toRingHom) := by
    apply IsFractionRing.ringHom_ext (A := R) (K := FractionRing R) (L := K)
    intro x
    simp [R, RingHom.comp_apply, coe_conjAutRingOfIntegers_apply]
  exact RingHom.congr_fun hhom z

/-- Fraction-field conjugation is involutive. -/
@[simp]
theorem conjAutFractionRingAlgEquiv_apply_apply [NumberField K] (z : FractionRing OK) :
    (conjAutFractionRingAlgEquiv K) ((conjAutFractionRingAlgEquiv K) z) = z := by
  apply (FractionRing.algEquiv OK K).injective
  rw [fractionRing_algEquiv_conjAutFractionRingAlgEquiv,
    fractionRing_algEquiv_conjAutFractionRingAlgEquiv]
  exact QuadraticField.Conj.conj_conj (K := K) (FractionRing.algEquiv OK K z)

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
  have hcard : Nat.card Gal(K / ℚ) = 2 := QuadraticField.card_aut_eq_two K
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

/-- The fraction-field Galois element induced by quadratic conjugation on the
ring of integers. -/
noncomputable def conjAutFractionRingGal [NumberField K] :
    Gal(FractionRing OK / FractionRing ℤ) := by
  exact (galRestrict ℤ (FractionRing ℤ) (FractionRing OK) OK).symm
    (conjAutRingOfIntegersAlgEquiv K)

/-- Restricting `conjAutFractionRingGal` back to the ring of integers recovers
the `ℤ`-algebra form of quadratic conjugation. -/
theorem galRestrict_conjAutFractionRingGal [NumberField K] :
    galRestrict ℤ (FractionRing ℤ) (FractionRing OK) OK
        (conjAutFractionRingGal K) =
      conjAutRingOfIntegersAlgEquiv K := by
  rw [conjAutFractionRingGal, MulEquiv.apply_symm_apply]

/-- The fraction-field Galois element induced by quadratic conjugation is
nontrivial. -/
theorem conjAutFractionRingGal_ne_one [NumberField K] :
    conjAutFractionRingGal K ≠ 1 := by
  intro hτ
  apply conjAutRingOfIntegersAlgEquiv_ne_refl (K := K)
  have h := congrArg
    (galRestrict ℤ (FractionRing ℤ) (FractionRing OK) OK) hτ
  simpa [galRestrict_conjAutFractionRingGal] using h

/-- The action of `conjAutFractionRingGal` on ideals is the same as mapping by
ring-of-integers conjugation. -/
theorem conjAutFractionRingGal_smul_ideal [NumberField K] (I : Ideal OK) :
    conjAutFractionRingGal K • I =
      Ideal.map (conjAutRingOfIntegers K : OK →+* OK) I := by
  change Ideal.map
    ((galRestrict ℤ (FractionRing ℤ) (FractionRing OK) OK (conjAutFractionRingGal K) :
        OK ≃ₐ[ℤ] OK) : OK →+* OK) I =
      Ideal.map (conjAutRingOfIntegers K : OK →+* OK) I
  rw [galRestrict_conjAutFractionRingGal]
  rfl

/-- Ring-of-integers conjugation is involutive. -/
@[simp]
theorem conjAutRingOfIntegers_apply_apply (x : OK) :
    (conjAutRingOfIntegers K) ((conjAutRingOfIntegers K) x) = x := by
  ext
  simpa [coe_conjAutRingOfIntegers_apply] using
    (QuadraticField.Conj.conj_conj (K := K) (x : K))

/-- The `ℤ`-algebra equivalence form of ring-of-integers conjugation is
involutive. -/
@[simp]
theorem conjAutRingOfIntegersAlgEquiv_apply_apply (x : OK) :
    (conjAutRingOfIntegersAlgEquiv K) ((conjAutRingOfIntegersAlgEquiv K) x) = x := by
  ext
  simpa [coe_conjAutRingOfIntegersAlgEquiv_apply] using
    (QuadraticField.Conj.conj_conj (K := K) (x : K))

/-- Applying the ring-of-integers conjugation twice fixes every ideal. -/
@[simp]
theorem map_conjAut_map_conjAut (I : Ideal OK) :
    Ideal.map (conjAutRingOfIntegers K : OK →+* OK)
        (Ideal.map (conjAutRingOfIntegers K : OK →+* OK) I) = I := by
  rw [Ideal.map_map]
  convert Ideal.map_id I
  ext x
  simp

end RingOfIntegersConjugation

end QuadraticNumberFields
