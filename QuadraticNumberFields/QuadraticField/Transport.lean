/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/

import QuadraticNumberFields.QuadraticField.Basic
import QuadraticNumberFields.Mathlib.RingTheory.DedekindDomain.Basic
import Mathlib.NumberTheory.NumberField.Discriminant.Defs
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex

/-!
# Transport for Abstract Quadratic Fields

This file collects lightweight transport lemmas for the standard workflow:
classify an abstract quadratic field as a model `Qsqrtd d`, compute in the
model, then transport invariant statements back along an algebra equivalence.

## Main definitions

* `QuadraticField.transportAlong`: transport the `QuadraticField` class across
  a `ℚ`-algebra equivalence.
* `QuadraticField.discr_eq_of_algEquiv`: transport absolute discriminants.
* `QuadraticField.ringOfIntegersEquivOfAlgEquiv`: transport rings of integers
  along an algebra equivalence.
* `QuadraticField.ringOfIntegersEquivOfRingEquiv`: transport rings of integers
  along a ring equivalence.
* `QuadraticField.isDedekindDomain_of_ringEquiv`: transport Dedekind-domain
  structure along a ring equivalence.
* `QuadraticField.isDedekindDomain_ringOfIntegers_of_ringEquiv`: transport
  Dedekind-domain structure for rings of integers.
* `QuadraticField.isTotallyReal_of_algEquiv` and
  `QuadraticField.isTotallyComplex_of_algEquiv`: transport infinite-place
  classification.
-/

open scoped NumberField

namespace QuadraticField

variable {K L : Type*} [Field K] [Algebra ℚ K] [Field L] [Algebra ℚ L]

/-- Transport the underlying mathlib quadratic-extension predicate across a
`ℚ`-algebra equivalence. -/
theorem isQuadraticExtension_of_algEquiv [QuadraticField K] (e : K ≃ₐ[ℚ] L) :
    Algebra.IsQuadraticExtension ℚ L where
  finrank_eq_two' := by
    have hK : Module.finrank ℚ K = 2 := Algebra.IsQuadraticExtension.finrank_eq_two ℚ K
    exact (LinearEquiv.finrank_eq e.toLinearEquiv).symm.trans hK

/-! The two following definitions return class instances intentionally; marking
them reducible lets instance search unfold them when a local transported
instance is introduced with `letI`. -/

/-- Transport the project-level `QuadraticField` class across a `ℚ`-algebra equivalence. -/
@[reducible]
def transportAlong [QuadraticField K] (e : K ≃ₐ[ℚ] L) : QuadraticField L where
  isQuadratic := isQuadraticExtension_of_algEquiv e

/-- Transport `QuadraticField` in the reverse direction across a `ℚ`-algebra equivalence. -/
@[reducible]
def transportBack [QuadraticField L] (e : K ≃ₐ[ℚ] L) : QuadraticField K :=
  transportAlong e.symm

/-- Trace is invariant under a `ℚ`-algebra equivalence: this is the project-level
wrapper of mathlib's `Algebra.trace_eq_of_algEquiv`. -/
theorem trace_eq_trace_of_algEquiv (e : K ≃ₐ[ℚ] L) (x : K) :
    Algebra.trace ℚ L (e x) = Algebra.trace ℚ K x :=
  Algebra.trace_eq_of_algEquiv e x

/-- Norm is invariant under a `ℚ`-algebra equivalence: this is the project-level
wrapper of mathlib's `Algebra.norm_eq_of_algEquiv`. -/
theorem norm_eq_norm_of_algEquiv (e : K ≃ₐ[ℚ] L) (x : K) :
    Algebra.norm ℚ (e x) = Algebra.norm ℚ x :=
  Algebra.norm_eq_of_algEquiv e x

/-- Absolute discriminants are invariant under `ℚ`-algebra equivalence. -/
theorem discr_eq_of_algEquiv [NumberField K] [NumberField L] (e : K ≃ₐ[ℚ] L) :
    NumberField.discr K = NumberField.discr L :=
  NumberField.discr_eq_discr_of_ringEquiv K e.toRingEquiv

/-- Transport rings of integers across a `ℚ`-algebra equivalence of number fields. -/
noncomputable def ringOfIntegersEquivOfAlgEquiv (e : K ≃ₐ[ℚ] L) :
    𝓞 K ≃+* 𝓞 L :=
  (e.restrictScalars ℤ).mapIntegralClosure.toRingEquiv

@[simp]
theorem ringOfIntegersEquivOfAlgEquiv_apply (e : K ≃ₐ[ℚ] L) (x : 𝓞 K) :
    (ringOfIntegersEquivOfAlgEquiv e).toFun x = (e (x : K) : L) := by
  rfl

@[simp]
theorem ringOfIntegersEquivOfAlgEquiv_symm_apply (e : K ≃ₐ[ℚ] L) (y : 𝓞 L) :
    (ringOfIntegersEquivOfAlgEquiv e).symm.toFun y = (e.symm (y : L) : K) := by
  rfl

/-- `ringOfIntegersEquivOfAlgEquiv` is natural: composing two equivalences
gives the ring-of-integers equivalence of the composite. -/
theorem ringOfIntegersEquivOfAlgEquiv_trans {M : Type*} [Field M] [Algebra ℚ M]
    (e : K ≃ₐ[ℚ] L) (f : L ≃ₐ[ℚ] M) :
    ringOfIntegersEquivOfAlgEquiv (e.trans f) =
      (ringOfIntegersEquivOfAlgEquiv e).trans (ringOfIntegersEquivOfAlgEquiv f) := by
  ext x
  rfl

/-- Transport rings of integers across a ring equivalence of fields. -/
noncomputable def ringOfIntegersEquivOfRingEquiv (e : K ≃+* L) :
    𝓞 K ≃+* 𝓞 L :=
  (AlgEquiv.ofRingEquiv (R := ℤ) (f := e) (fun n => by
    simp only [eq_intCast, map_intCast])).mapIntegralClosure.toRingEquiv

/-- Transport the Dedekind-domain property across a ring equivalence. -/
theorem isDedekindDomain_of_ringEquiv
    {F E : Type*} [Field F] [Field E] [IsDedekindDomain F] (e : F ≃+* E) :
    IsDedekindDomain E :=
  RingEquiv.isDedekindDomain e

/-- Transport the Dedekind-domain property for rings of integers across a ring
equivalence of fields. -/
theorem isDedekindDomain_ringOfIntegers_of_ringEquiv
    {F E : Type*} [Field F] [Field E] [IsDedekindDomain (𝓞 F)] (e : F ≃+* E) :
    IsDedekindDomain (𝓞 E) :=
  RingEquiv.isDedekindDomain (ringOfIntegersEquivOfRingEquiv e)

/-- Transport total reality across a `ℚ`-algebra equivalence. -/
theorem isTotallyReal_of_algEquiv [NumberField.IsTotallyReal K] (e : K ≃ₐ[ℚ] L) :
    NumberField.IsTotallyReal L :=
  NumberField.IsTotallyReal.ofRingEquiv e.toRingEquiv

/-- Total reality is invariant under a `ℚ`-algebra equivalence. -/
theorem isTotallyReal_iff_of_algEquiv (e : K ≃ₐ[ℚ] L) :
    NumberField.IsTotallyReal K ↔ NumberField.IsTotallyReal L :=
  NumberField.isTotallyReal_iff_ofRingEquiv e.toRingEquiv

/-- Transport total complexity across a `ℚ`-algebra equivalence. -/
theorem isTotallyComplex_of_algEquiv [NumberField.IsTotallyComplex K] (e : K ≃ₐ[ℚ] L) :
    NumberField.IsTotallyComplex L where
  isComplex w := by
    exact NumberField.InfinitePlace.IsComplex.of_comap e.toRingHom
      (NumberField.IsTotallyComplex.isComplex (w.comap e.toRingHom))

/-- Total complexity is invariant under a `ℚ`-algebra equivalence. -/
theorem isTotallyComplex_iff_of_algEquiv (e : K ≃ₐ[ℚ] L) :
    NumberField.IsTotallyComplex K ↔ NumberField.IsTotallyComplex L :=
  ⟨fun h => by
    letI := h
    exact isTotallyComplex_of_algEquiv e,
   fun h => by
    letI := h
    exact isTotallyComplex_of_algEquiv e.symm⟩

end QuadraticField
