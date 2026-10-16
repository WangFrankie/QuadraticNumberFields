/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/

import QuadraticNumberFields.QuadraticField.Basic
import QNFMathlib.RingTheory.DedekindDomain.Basic
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
* `NumberField.discr_eq_of_algEquiv`: transport absolute discriminants.
* `AlgEquiv.ringOfIntegers`: transport rings of integers along an algebra
  equivalence.
* `RingEquiv.ringOfIntegers`: transport rings of integers along a ring equivalence.
* `RingEquiv.isDedekindDomain_ringOfIntegers`: transport
  Dedekind-domain structure for rings of integers.
* `NumberField.IsTotallyReal.ofAlgEquiv` and
  `NumberField.IsTotallyComplex.ofAlgEquiv`: transport infinite-place
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

set_option linter.defProp false in
/-- Transport the `QuadraticField` class across a `ℚ`-algebra equivalence. -/
@[reducible]
def transportAlong [QuadraticField K] (e : K ≃ₐ[ℚ] L) : QuadraticField L where
  isQuadratic := isQuadraticExtension_of_algEquiv e

set_option linter.defProp false in
/-- Transport `QuadraticField` in the reverse direction across a `ℚ`-algebra equivalence. -/
@[reducible]
def transportBack [QuadraticField L] (e : K ≃ₐ[ℚ] L) : QuadraticField K :=
  transportAlong e.symm

end QuadraticField

namespace NumberField

variable {K L : Type*} [Field K] [Algebra ℚ K] [Field L] [Algebra ℚ L]

-- Upstream-location candidate:
-- `Mathlib.NumberTheory.NumberField.Discriminant.Defs`.
-- Kept here until a dedicated mathlib PR also moves the imports and callers.
/-- Absolute discriminants are invariant under `ℚ`-algebra equivalence. -/
theorem discr_eq_of_algEquiv [NumberField K] [NumberField L] (e : K ≃ₐ[ℚ] L) :
    discr K = discr L :=
  NumberField.discr_eq_discr_of_ringEquiv K e.toRingEquiv

end NumberField

namespace AlgEquiv

variable {K L : Type*} [Field K] [Algebra ℚ K] [Field L] [Algebra ℚ L]

-- Upstream-location candidate:
-- a number-field/ring-of-integers file, chosen with the eventual mathlib PR.
-- Kept here because the local caller set is still small and import-neutral.
/-- Transport rings of integers across a `ℚ`-algebra equivalence of number fields. -/
noncomputable def ringOfIntegers (e : K ≃ₐ[ℚ] L) :
    𝓞 K ≃+* 𝓞 L :=
  (e.restrictScalars ℤ).mapIntegralClosure.toRingEquiv

/-- The induced equivalence on rings of integers agrees with the underlying
`ℚ`-algebra equivalence. -/
@[simp]
theorem ringOfIntegers_apply (e : K ≃ₐ[ℚ] L) (x : 𝓞 K) :
    (e.ringOfIntegers x : L) = e (x : K) := by
  rfl

/-- The inverse equivalence on rings of integers agrees with the inverse
`ℚ`-algebra equivalence. -/
@[simp]
theorem ringOfIntegers_symm_apply (e : K ≃ₐ[ℚ] L) (y : 𝓞 L) :
    ((e.ringOfIntegers : 𝓞 K ≃+* 𝓞 L).symm y : K) = e.symm (y : L) := by
  rfl

/-- `AlgEquiv.ringOfIntegers` is natural: composing two equivalences
gives the ring-of-integers equivalence of the composite. -/
theorem ringOfIntegers_trans {M : Type*} [Field M] [Algebra ℚ M]
    (e : K ≃ₐ[ℚ] L) (f : L ≃ₐ[ℚ] M) :
    (e.trans f).ringOfIntegers = e.ringOfIntegers.trans f.ringOfIntegers := by
  ext x
  rfl

end AlgEquiv

namespace RingEquiv

variable {K L : Type*} [Field K] [Algebra ℚ K] [Field L] [Algebra ℚ L]

-- Upstream-location candidate:
-- a number-field/ring-of-integers file, chosen with the eventual mathlib PR.
-- Kept here because the local caller set is still small and import-neutral.
/-- Transport rings of integers across a ring equivalence of fields. -/
noncomputable def ringOfIntegers (e : K ≃+* L) :
    𝓞 K ≃+* 𝓞 L :=
  (AlgEquiv.ofRingEquiv (R := ℤ) (f := e) (fun n => by
    simp only [eq_intCast, map_intCast])).mapIntegralClosure.toRingEquiv

/-- Transport the Dedekind-domain property for rings of integers across a ring
equivalence of fields. -/
theorem isDedekindDomain_ringOfIntegers
    {F E : Type*} [Field F] [Field E] [IsDedekindDomain (𝓞 F)] (e : F ≃+* E) :
    IsDedekindDomain (𝓞 E) :=
  RingEquiv.isDedekindDomain e.ringOfIntegers

end RingEquiv

namespace NumberField

namespace IsTotallyReal

variable {K L : Type*} [Field K] [Algebra ℚ K] [Field L] [Algebra ℚ L]

-- Upstream-location candidate:
-- `Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex`.
-- Kept here until a dedicated mathlib PR also moves the imports and callers.
/-- Transport total reality across a `ℚ`-algebra equivalence. -/
theorem ofAlgEquiv [IsTotallyReal K] (e : K ≃ₐ[ℚ] L) :
    IsTotallyReal L :=
  ofRingEquiv e.toRingEquiv

end IsTotallyReal

variable {K L : Type*} [Field K] [Algebra ℚ K] [Field L] [Algebra ℚ L]

/-- Total reality is invariant under a `ℚ`-algebra equivalence. -/
theorem isTotallyReal_iff_ofAlgEquiv (e : K ≃ₐ[ℚ] L) :
    IsTotallyReal K ↔ IsTotallyReal L :=
  NumberField.isTotallyReal_iff_ofRingEquiv e.toRingEquiv

namespace IsTotallyComplex

variable {K L : Type*} [Field K] [Algebra ℚ K] [Field L] [Algebra ℚ L]

-- Upstream-location candidate:
-- `Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex`.
-- Kept here until a dedicated mathlib PR also moves the imports and callers.
/-- Transport total complexity across a `ℚ`-algebra equivalence. -/
theorem ofAlgEquiv [IsTotallyComplex K] (e : K ≃ₐ[ℚ] L) :
    IsTotallyComplex L where
  isComplex w :=
    NumberField.InfinitePlace.IsComplex.of_comap e.toRingHom
      (NumberField.IsTotallyComplex.isComplex (w.comap e.toRingHom))

end IsTotallyComplex

variable {K L : Type*} [Field K] [Algebra ℚ K] [Field L] [Algebra ℚ L]

/-- Total complexity is invariant under a `ℚ`-algebra equivalence. -/
theorem isTotallyComplex_iff_ofAlgEquiv (e : K ≃ₐ[ℚ] L) :
    IsTotallyComplex K ↔ IsTotallyComplex L :=
  ⟨fun h => by
    letI := h
    exact IsTotallyComplex.ofAlgEquiv e,
   fun h => by
    letI := h
    exact IsTotallyComplex.ofAlgEquiv e.symm⟩

end NumberField
